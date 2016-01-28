(** Equality checking and weak-head-normal-forms *)

(** Notation for the monads bind *)

module AtomSet = Name.AtomSet

(* XXX we seem to use Monad only to lift to Opt and trivially in the as_* functions, so merge with Opt? *)
module Monad = struct
  type state = AtomSet.t

  let empty = AtomSet.empty

  type 'a t =
    { k : 'r. ('a -> state -> 'r Value.result) -> state -> 'r Value.result }

  let return x =
    { k = fun c s -> c x s }

  let (>>=) m f =
    { k = fun c s -> m.k (fun x s -> (f x).k c s) s }

  (* lift : 'a Value.result -> 'a t *)
  let lift m =
    { k = fun c s -> Value.bind m (fun x -> c x s) }

  let modify f =
    { k = fun c s -> c () (f s) }

  let add_hyps hyps = modify (AtomSet.union hyps)

  (** The implicit equality witness [ctx, ys, zs |- e] is replaced by [ctx |- lambda ys, e[es/zs]] *)
  let context_abstract ~loc ctx ys ts =
    lift (Matching.context_abstract ~loc ctx ys ts) >>= fun (ctx,zs,es) ->
    modify (fun hyps ->
      let hyps = List.fold_left2 (fun hyps z e ->
          if AtomSet.mem z hyps
          then
            let hyps = AtomSet.remove z hyps in
            let hyps_e = Tt.assumptions_term e in
            let hyps = AtomSet.union hyps hyps_e in
            hyps
          else hyps)
        hyps zs es
      in
      List.fold_left (fun hyps y -> AtomSet.remove y hyps) hyps ys) >>= fun () ->
    return ctx

  let run m =
    m.k (fun x s -> Value.return (x,s)) empty
end

module Opt = struct
  type state = Monad.state

  type 'a opt =
    { k : 'r. ('a -> state -> 'r Value.result) -> (state -> 'r Value.result) -> state -> 'r Value.result }

  let return x =
    { k = fun sk _ s -> sk x s }

  let (>?=) m f =
    { k = fun sk fk s -> m.k (fun x s -> (f x).k sk fk s) fk s }

  let unfailing (m : 'a Monad.t) : 'a opt =
    { k = fun sk _ s -> m.Monad.k sk s }

  let fail =
    { k = fun _ fk s -> fk s }

  let locally (m : 'a opt) : ('a*state) opt =
    { k = fun sk fk s -> m.k (fun x s' -> sk (x,s') (AtomSet.union s s')) fk Monad.empty }

  (* I have no clue if this does the right thing *)
  let add_free ~loc x j m =
    { k = fun sk fk s ->
          Value.add_free ~loc x j (fun ctx z -> (m ctx z).k (fun y s' -> (sk y s')) fk s) }

  let add_abstracting ~loc x j m =
    { k = fun sk fk s ->
          Value.add_abstracting ~loc x j (fun ctx z -> (m ctx z).k (fun y s' -> (sk y s')) fk s) }

  let run m =
    m.k (fun x s -> Value.return (Some (x,s))) (fun _ -> Value.return None) AtomSet.empty
end

let (>>=) = Monad.(>>=)

let (>?=) = Opt.(>?=)

let (>!=) m f = (Opt.unfailing m) >?= f

(* counter for debugging depth  *)
let cnt = let msg_cnt = ref (-1) in fun () -> (incr msg_cnt; !msg_cnt)


(** Compare two types *)
let rec equal ctx ({Tt.loc=loc1;_} as e1) ({Tt.loc=loc2;_} as e2) t =
  Monad.lift Value.print_term >!= fun pte -> Monad.lift Value.print_ty >!= fun pty ->
  let i = cnt () in
  Print.debug "(%i checking equality of@ %t@ and@ %t@ at type@ %t" i
    (pte e1) (pte e2) (pty t);
  if Tt.alpha_equal e1 e2
  then Opt.return ctx
  else
    Monad.lift (Value.perform_equal
        (Value.mk_term (Jdg.mk_term ctx e1 t))
        (Value.mk_term (Jdg.mk_term ctx e2 t))) >!= fun v ->
    let loc = loc1 in
    match Value.as_option ~loc v with
      | Some v ->
        let Jdg.Term (ctxeq,eq,teq) = Value.as_term ~loc v in
        let ctx = Context.join ~loc ctx ctxeq in
        Monad.add_hyps (Tt.assumptions_term eq) >!= fun () ->
        let tgoal = Tt.mk_eq_ty ~loc t e1 e2 in
        equal_ty ctx teq tgoal
      | None -> Opt.fail

and equal_ty ctx (Tt.Ty t1) (Tt.Ty t2) = equal ctx t1 t2 Tt.typ


let equal_signature ~loc ctx xts1 xts2 =
  let rec fold ctx ys ys' ts xts1 xts2 = match xts1, xts2 with
    | [], [] ->
      Monad.context_abstract ~loc ctx ys ts >!= fun ctx ->
      Opt.return ctx
    | (l1,x,t1)::xts1, (l2,_,t2)::xts2 ->
      if Name.eq_ident l1 l2
      then
        let t1 = Tt.unabstract_ty ys t1 in
        let t2 = Tt.instantiate_ty ys' t2 in
        Opt.locally (equal_ty ctx t1 t2) >?= fun (ctx,hypst) ->
        let jx = Jdg.mk_ty ctx t1 in
        Opt.add_free ~loc x jx (fun ctx y ->
        let y' = Tt.mention_atoms hypst (Tt.mk_atom ~loc y) in
        fold ctx (y::ys) (y'::ys') (t1::ts) xts1 xts2)
      else Opt.fail
    | _::_,[] | [],_::_ -> Opt.fail
    in
  fold ctx [] [] [] xts1 xts2

(** this function assumes that the derived signatures have already been checked equal label to label *)
and equal_module ~loc ctx xtes1 xtes2 =
  let rec fold ctx vs xtes1 xtes2 = match xtes1, xtes2 with
    | [], [] ->
      Opt.return ctx
    | (l1,x,t1,te1)::xts1, (l2,_,t2,te2)::xts2 ->
      (* TODO we do not use t2 so the call to equal_module should send the common signature *)
      if Name.eq_ident l1 l2
      then
        let ty = Tt.instantiate_ty vs t1 in (* here we need to know that ctx |- instantiate t1 == instantiate t2. Is this true? *)
        let te1 = Tt.instantiate vs te1 in
        let te2 = Tt.instantiate vs te2 in
        equal ctx te1 te2 ty >?= fun ctx ->
        fold ctx (te1::vs) xts1 xts2
      else Opt.fail
    | _::_,[] | [],_::_ -> Opt.fail
    in
  fold ctx [] xtes1 xtes2

(** Apply the appropriate congruence rule *)
let congruence ~loc ctx ({Tt.term=e1';loc=loc1;_} as e1) ({Tt.term=e2';loc=loc2;_} as e2) t =
  Print.debug "congruence of %t and %t"
              (Tt.print_term [] e1)
              (Tt.print_term [] e2) ;
  match e1', e2' with

  | Tt.Atom x, Tt.Atom y ->
     if Name.eq_atom x y then Opt.return ctx
     else Opt.fail

  | Tt.Bound _, _ | _, Tt.Bound _ ->
     Error.impossible ~loc "deBruijn encountered in congruence"

  | Tt.Constant x, Tt.Constant y ->
     if Name.eq_ident x y then Opt.return ctx
     else Opt.fail

  | Tt.Lambda ((x,a1), (e1, t1)), Tt.Lambda ((_,a2), (e2, t2)) ->
    Opt.locally (equal_ty ctx a1 a2) >?= fun (ctx,hypsa) ->
    let ja = Jdg.mk_ty ctx a1 in
    Opt.add_abstracting ~loc x ja (fun ctx y ->
    let y' = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
    let e1 = Tt.unabstract [y] e1
    and t1 = Tt.unabstract_ty [y] t1
    and e2 = Tt.instantiate [y'] e2
    and t2 = Tt.instantiate_ty [y'] t2 in
    Opt.locally (equal_ty ctx t1 t2) >?= fun (ctx,hypst) ->
    let e2 = Tt.mention_atoms hypst e2 in
    equal ctx e1 e2 t1 >?= fun ctx ->
    Monad.context_abstract ~loc ctx [y] [a1] >!= fun ctx ->
    Opt.return ctx)

  | Tt.Apply (h1, ((x,a1),b1), e1), Tt.Apply (h2, ((_,a2),b2), e2) ->
    Opt.locally (equal_ty ctx a1 a2) >?= fun (ctx,hypsa) ->
    Opt.locally (Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a1) (fun ctx y ->
      let y' = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
      let b1 = Tt.unabstract_ty [y] b1
      and b2 = Tt.instantiate_ty [y'] b2 in
      equal_ty ctx b1 b2 >?= fun ctx ->
      Monad.context_abstract ~loc ctx [y] [a1] >!= fun ctx ->
      Opt.return ctx)) >?= fun (ctx,hypsb) ->
    let prod = Tt.mk_prod_ty ~loc x a1 b1 in
    let h2 = Tt.mention_atoms hypsb (Tt.mention_atoms hypsa h2) in
    equal ctx h1 h2 prod >?= fun ctx ->
    let e2 = Tt.mention_atoms hypsa e2 in
    equal ctx e1 e2 a1

  | Tt.Type, Tt.Type -> Opt.return ctx

  | Tt.Prod ((x,a1), b1), Tt.Prod ((_,a2), b2) ->
    Opt.locally (equal_ty ctx a1 a2) >?= fun (ctx,hypsa) ->
    Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a1) (fun ctx y ->
    let y' = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
    let b1 = Tt.unabstract_ty [y] b1
    and b2 = Tt.instantiate_ty [y'] b2 in
    equal_ty ctx b1 b2 >?= fun ctx ->
    Monad.context_abstract ~loc ctx [y] [a1] >!= fun ctx ->
    Opt.return ctx)

  | Tt.Eq (u, d1, d2), Tt.Eq (u', d1', d2') ->
     Opt.locally (equal_ty ctx u u') >?= fun (ctx,hyps) ->
     equal ctx d1 (Tt.mention_atoms hyps d1') u >?= fun ctx ->
     equal ctx d2 (Tt.mention_atoms hyps d2') u

  | Tt.Refl (u, d), Tt.Refl (u', d') ->
     Opt.locally (equal_ty ctx u u') >?= fun (ctx,hyps) ->
     equal ctx d (Tt.mention_atoms hyps d') u

  | Tt.Signature xts1, Tt.Signature xts2 -> equal_signature ~loc:loc1 ctx xts1 xts2

  | Tt.Structure xtes1, Tt.Structure xtes2 ->
    let xts1 = List.map (fun (l,x,t,_) -> l,x,t) xtes1 in
    let xts2 = List.map (fun (l,x,t,_) -> l,x,t) xtes2 in
    Opt.locally (equal_signature ~loc:loc1 ctx xts1 xts2) >?= fun (ctx, hyps) ->
    (* XXX TODO be more precise about which part of hyps is needed where *)
    let xtes2 = List.map (fun (l, x, t, e) -> (l, x, t, Tt.mention_atoms hyps e)) xtes2 in
    equal_module ~loc:loc1 ctx xtes1 xtes2

  | Tt.Projection (te1,xts1,p1), Tt.Projection (te2,xts2,p2) ->
    if Name.eq_ident p1 p2
    then
      Opt.locally (equal_signature ~loc:loc1 ctx xts1 xts2) >?= fun (ctx,hyps) ->
      let t = Tt.mk_signature_ty ~loc:loc1 xts1 in
      let te2 = Tt.mention_atoms hyps te2 in
      equal ctx te1 te2 t
    else Opt.fail

  | (Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Apply _ |
     Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _ |
     Tt.Signature _ | Tt.Structure _ | Tt.Projection _), _ ->
     Opt.fail

(** Beta reduction of [Lambda ((x,a), (e, b))] applied to argument [e'],
    where [((x,a'), b')] is the typing annotation for the application.
    Returns the resulting expression. *)
let beta_reduce ~loc ctx (x,a) e b (_,a') b' e' =
  Opt.locally (equal_ty ctx a a') >?= fun (ctx,hypsa) ->
  Opt.locally (Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a) (fun ctx y ->
    let y' = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
    let b = Tt.unabstract_ty [y] b
    and b' = Tt.instantiate_ty [y'] b' in
    equal_ty ctx b b' >?= fun ctx ->
    Monad.context_abstract ~loc ctx [y] [a] >!= fun ctx ->
    Opt.return ctx)) >?= fun (ctx,hypsb) ->
  let e' = Tt.mention_atoms hypsa e' in
  let e = Tt.instantiate [e'] e in
  let e = Tt.mention_atoms hypsb e in
  Opt.return (ctx,e)

(** Reduction of [{xtes}.p] at type [{xts}] *)
let projection_reduce ~loc ctx xts p xtes =
  equal_signature ~loc ctx xts (List.map (fun (l,x,t,_) -> l,x,t) xtes) >?= fun ctx ->
  let te = Tt.field_value ~loc xtes p in
  Opt.return (ctx,te)

let reduce_step ctx {Tt.term=e'; assumptions; loc} =
  match e' with
  | Tt.Apply (e1, (xts, t), e2) ->
     begin match e1.Tt.term with
           | Tt.Lambda (xus, (e', u)) ->
              beta_reduce ~loc ctx xus e' u xts t e2 >?= fun (ctx, e) ->
              Opt.return (ctx, Tt.mention assumptions e)
           | Tt.Atom _
           | Tt.Constant _
           | Tt.Apply _
           | Tt.Type
           | Tt.Prod _
           | Tt.Eq _
           | Tt.Refl _
           | Tt.Signature _
           | Tt.Structure _
           | Tt.Projection _ -> Opt.fail
           | Tt.Bound _ ->
              Error.impossible ~loc "de Bruijn encountered in an apply head in reduce"
     end

  | Tt.Projection (e,xts,p) ->
     begin
       match e.Tt.term with
       | Tt.Structure xtes ->
          projection_reduce ~loc ctx xts p xtes >?= fun (ctx, e) ->
          Opt.return (ctx, Tt.mention assumptions e)
       | Tt.Atom _
       | Tt.Constant _
       | Tt.Lambda _
       | Tt.Apply _
       | Tt.Type
       | Tt.Prod _
       | Tt.Eq _
       | Tt.Refl _
       | Tt.Signature _
       | Tt.Projection _ -> Opt.fail
       | Tt.Bound _ ->
          Error.impossible ~loc "de Bruijn encountered in a projection head in reduce"
     end

  | Tt.Constant _
  | Tt.Lambda _
  | Tt.Prod _
  | Tt.Atom _
  | Tt.Type
  | Tt.Eq _
  | Tt.Refl _
  | Tt.Signature _
  | Tt.Structure _ -> Opt.fail
  | Tt.Bound _ ->
     Error.impossible ~loc "de Bruijn encountered in reduce"


let as_eq_alpha (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t))) =
  match t' with
    | Tt.Eq (t, e1, e2) -> Monad.return (t, e1, e2)
    | _ ->
      Monad.lift Value.print_ty >>= fun pty ->
      Error.typing ~loc "this expression should be an equality, found@ %t"
          (pty t)

let as_eq (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Eq (t, e1, e2) -> Monad.return (ctx, t, e1, e2)
    | _ ->
      Monad.lift (Value.perform_as_eq (Value.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Value.as_option ~loc v with
        | None ->
          Monad.lift Value.print_ty >>= fun pty ->
          Error.typing ~loc "this expression should be an equality, found@ %t"
              (pty t)
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Value.as_term ~loc v in
          as_eq_alpha (Jdg.mk_ty ctxv tv) >>= fun (tv,e1,e2) ->
          if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
          then
            as_eq_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) >>= fun (t,e1,e2) ->
            let ctx = Context.join ~loc ctx ctxv in
            let hyps = Tt.assumptions_term ev in
            Monad.add_hyps hyps >>= fun () ->
            Monad.return (ctx,t,e1,e2)
          else
            Monad.lift (Value.print_ty) >>= fun pty ->
            Error.typing ~loc:ev.Tt.loc
                "this expression should be a witness of equality between %t and an equality"
                (pty t)
      end

let as_prod_alpha (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t))) =
  match t' with
    | Tt.Prod (xts,t) -> Monad.return (xts,t)
    | _ ->
      Monad.lift Value.print_ty >>= fun pty ->
      Error.typing ~loc "this expression should be a product, found@ %t"
          (pty t)

let as_prod (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Prod (xts,t) -> Monad.return (ctx, (xts,t))
    | _ ->
      Monad.lift (Value.perform_as_prod (Value.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Value.as_option ~loc v with
        | None ->
          Monad.lift Value.print_ty >>= fun pty ->
          Error.typing ~loc "this expression should be an equality, found@ %t"
              (pty t)
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Value.as_term ~loc v in
          as_eq_alpha (Jdg.mk_ty ctxv tv) >>= fun (tv,e1,e2) ->
          if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
          then
            as_prod_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) >>= fun (xts,t) ->
            let ctx = Context.join ~loc ctx ctxv in
            let hyps = Tt.assumptions_term ev in
            Monad.add_hyps hyps >>= fun () ->
            Monad.return (ctx,(xts,t))
          else
            Monad.lift (Value.print_ty) >>= fun pty ->
            Error.typing ~loc:ev.Tt.loc
                "this expression should be a witness of equality between %t and a product"
                (pty t)
      end

let as_signature_alpha (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t))) =
  match t' with
    | Tt.Signature xts -> Monad.return xts
    | _ ->
      Monad.lift Value.print_ty >>= fun pty ->
      Error.typing ~loc "this expression should be a signature, found@ %t"
          (pty t)


let as_signature (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Signature xts -> Monad.return (ctx, xts)
    | _ ->
      Monad.lift (Value.perform_as_signature (Value.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Value.as_option ~loc v with
        | None ->
          Monad.lift Value.print_ty >>= fun pty ->
          Error.typing ~loc "this expression should be an equality, found@ %t"
              (pty t)
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Value.as_term ~loc v in
          as_eq_alpha (Jdg.mk_ty ctxv tv) >>= fun (tv,e1,e2) ->
          if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
          then
            as_signature_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) >>= fun xts ->
            let ctx = Context.join ~loc ctx ctxv in
            let hyps = Tt.assumptions_term ev in
            Monad.add_hyps hyps >>= fun () ->
            Monad.return (ctx,xts)
          else
            Monad.lift (Value.print_ty) >>= fun pty ->
            Error.typing ~loc:ev.Tt.loc
                "this expression should be a witness of equality between %t and a product"
                (pty t)
      end

