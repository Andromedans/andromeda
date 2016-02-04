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

  let context_abstract ~loc ctx y t =
    lift Value.lookup_penv >>= fun penv ->
    let ctx = Context.abstract ~penv ~loc ctx y t in
    modify (fun hyps -> AtomSet.remove y hyps) >>= fun () ->
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
  Monad.lift Value.print_term >!= fun pte ->
  Monad.lift Value.print_ty >!= fun pty ->
  let i = cnt () in
  Print.debug "(%i checking equality of@ %t@ and@ %t@ at type@ %t" i
    (pte e1) (pte e2) (pty t);
  if Tt.alpha_equal e1 e2
  then
    Opt.return ctx
  else
    Monad.lift (Value.operation_equal
        (Value.mk_term (Jdg.mk_term ctx e1 t))
        (Value.mk_term (Jdg.mk_term ctx e2 t))) >!= fun v ->
    let loc = loc1 in
    match Value.as_option ~loc v with
      | Some v ->
        let Jdg.Term (ctxeq,eq,teq) = Value.as_term ~loc v in
        Monad.lift Value.lookup_penv >!= fun penv ->
        let ctx = Context.join ~penv ~loc ctx ctxeq in
        Monad.add_hyps (Tt.assumptions_term eq) >!= fun () ->
        let tgoal = Tt.mk_eq_ty ~loc t e1 e2 in
        equal_ty ctx teq tgoal
      | None -> Opt.fail

and equal_ty ctx (Tt.Ty t1) (Tt.Ty t2) = equal ctx t1 t2 Tt.typ

(** this function assumes that the derived signatures have already been checked equal label to label *)
and equal_structure ~loc ctx s_def es1 es2 =
  let rec fold ctx vs hyps fields es1 es2 =
    match fields, es1, es2 with
    | [], [], [] ->
       Opt.return ctx

    | (l,x,t)::fields, e1::es1, e2::es2 ->
        let t = Tt.instantiate_ty vs t in
        let e1 = Tt.instantiate vs e1 in
        let e2 = Tt.instantiate vs e2 in
        let e2 = Tt.mention_atoms hyps e2 in
        Opt.locally (equal ctx e1 e2 t) >?= fun (ctx, hyps') ->
        let hyps = AtomSet.union hyps hyps' in
        fold ctx (e1::vs) hyps fields es1 es2

    | _, _, _ ->
       Error.impossible ~loc "equal_structure: unequal lengths"
    in
  fold ctx [] AtomSet.empty s_def es1 es2

(** Apply the appropriate congruence rule *)
let congruence ~loc ctx ({Tt.term=e1';loc=loc1;_} as e1) ({Tt.term=e2';loc=loc2;_} as e2) t =
  Monad.lift Value.lookup_penv >!= fun penv ->
  Print.debug "congruence of %t and %t"
              (Tt.print_term ~penv e1)
              (Tt.print_term ~penv e2) ;
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
    Monad.context_abstract ~loc ctx y a1 >!= fun ctx ->
    Opt.return ctx)

  | Tt.Apply (h1, ((x,a1),b1), e1), Tt.Apply (h2, ((_,a2),b2), e2) ->
    Opt.locally (equal_ty ctx a1 a2) >?= fun (ctx,hypsa) ->
    Opt.locally (Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a1) (fun ctx y ->
      let y' = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
      let b1 = Tt.unabstract_ty [y] b1
      and b2 = Tt.instantiate_ty [y'] b2 in
      equal_ty ctx b1 b2 >?= fun ctx ->
      Monad.context_abstract ~loc ctx y a1 >!= fun ctx ->
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
    Monad.context_abstract ~loc ctx y a1 >!= fun ctx ->
    Opt.return ctx)

  | Tt.Eq (u, d1, d2), Tt.Eq (u', d1', d2') ->
     Opt.locally (equal_ty ctx u u') >?= fun (ctx,hyps) ->
     equal ctx d1 (Tt.mention_atoms hyps d1') u >?= fun ctx ->
     equal ctx d2 (Tt.mention_atoms hyps d2') u

  | Tt.Refl (u, d), Tt.Refl (u', d') ->
     Opt.locally (equal_ty ctx u u') >?= fun (ctx,hyps) ->
     equal ctx d (Tt.mention_atoms hyps d') u

  | Tt.Signature s1, Tt.Signature s2 ->
     if Name.eq_ident s1 s2
     then Opt.return ctx
     else Opt.fail

  | Tt.Structure (s1, lst1), Tt.Structure (s2, lst2) ->
     if Name.eq_ident s1 s2
     then
       Monad.lift (Value.lookup_signature s1) >!=
         begin function
           | None -> Error.impossible ~loc "Equal.congruence: unknown signature %t"
                                      (Name.print_ident s1)
           | Some s_def -> equal_structure ~loc:loc1 ctx s_def lst1 lst2
         end
     else Opt.fail

  | Tt.Projection (e1, s1, l1), Tt.Projection (e2, s2, l2) ->
     if Name.eq_ident l1 l2 && Name.eq_ident s1 s2
     then
       let t = Tt.mk_signature_ty ~loc:loc1 s1 in 
       equal ctx e1 e2 t
     else Opt.fail

  | (Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Apply _ |
     Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _ |
     Tt.Signature _ | Tt.Structure _ | Tt.Projection _), _ ->
     Opt.fail


let extensionality ~loc ctx e1 e2 (Tt.Ty t') =
  match t'.Tt.term with
  | Tt.Prod ((x, a), b) ->
     Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a) (fun ctx y ->
       let yt = Tt.mk_atom ~loc y in
       let e1' = Tt.mk_apply ~loc e1 x a b yt in
       let e2' = Tt.mk_apply ~loc e2 x a b yt in
       let b' = Tt.unabstract_ty [y] b in
       equal ctx e1' e2' b' >?= fun ctx ->
       Monad.context_abstract ~loc ctx y a >!= fun ctx ->
         Opt.return ctx)

  | Tt.Eq _ -> Opt.return ctx

  | Tt.Signature s ->
     Monad.lift (Value.lookup_signature s) >!=
       begin function
         | None -> Error.impossible ~loc "Equal.extensionality: unknown signature %t"
                                    (Name.print_ident s)
         | Some s_def -> 
            let rec fold ctx es hyps fields =
              match fields with
              | [] -> Opt.return ctx
              | (l, _, t) :: fields ->
                 let t = Tt.instantiate_ty es t in
                 let e1_proj = Tt.mk_projection ~loc:e1.Tt.loc e1 s l in
                 let e2_proj = Tt.mk_projection ~loc:e2.Tt.loc e2 s l in
                 let e2_proj = Tt.mention_atoms hyps e2_proj in
                 Opt.locally (equal ctx e1_proj e2_proj t) >?= fun (ctx, hyps') ->
                 let hyps = AtomSet.union hyps hyps' in
                 fold ctx (e1_proj :: es) hyps fields                                                               
            in
            fold ctx [] AtomSet.empty s_def
       end

  | Tt.Type | Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Apply _
  | Tt.Refl _ | Tt.Structure _ | Tt.Projection _ ->
      Opt.fail

  | Tt.Bound _ ->
     Error.impossible ~loc "deBruijn encountered in extensionality"
                                  


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
    Monad.context_abstract ~loc ctx y a >!= fun ctx ->
    Opt.return ctx)) >?= fun (ctx,hypsb) ->
  let e' = Tt.mention_atoms hypsa e' in
  let e = Tt.instantiate [e'] e in
  let e = Tt.mention_atoms hypsb e in
  Opt.return (ctx,e)

let reduction_step ctx {Tt.term=e'; assumptions; loc} =
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

  | Tt.Projection (e, s, l) ->
     begin
       match e.Tt.term with
       | Tt.Structure (s', es) ->
          if Name.eq_ident s s'
          then
            Monad.lift (Value.lookup_signature s) >!=
              begin function
                | None -> Error.impossible ~loc "unknown signature %t in reduce"
                                           (Name.print_ident s)
                | Some s_def ->
                   let e = Tt.field_value s_def es l ~loc in
                   Opt.return (ctx, Tt.mention assumptions e)
              end
          else Opt.fail

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
      Monad.lift (Value.operation_as_eq (Value.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
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
            Monad.lift Value.lookup_penv >>= fun penv ->
            let ctx = Context.join ~penv ~loc ctx ctxv in
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
      Monad.lift (Value.operation_as_prod (Value.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Value.as_option ~loc v with
        | None ->
          Monad.lift Value.print_ty >>= fun pty ->
          Error.typing ~loc "this expression should be a product, found@ %t"
              (pty t)
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Value.as_term ~loc v in
          as_eq_alpha (Jdg.mk_ty ctxv tv) >>= fun (tv,e1,e2) ->
          if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
          then
            as_prod_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) >>= fun (xts,t) ->
            Monad.lift Value.lookup_penv >>= fun penv ->
            let ctx = Context.join ~penv ~loc ctx ctxv in
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
    | Tt.Signature s -> Monad.return s
    | _ ->
      Monad.lift Value.print_ty >>= fun pty ->
      Error.typing ~loc "this expression should be a signature, found@ %t"
          (pty t)


let as_signature (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Signature s -> Monad.return (ctx, s)
    | _ ->
      Monad.lift (Value.operation_as_signature (Value.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Value.as_option ~loc v with
        | None ->
          Monad.lift Value.print_ty >>= fun pty ->
          Error.typing ~loc "this expression should be a signature, found@ %t"
              (pty t)
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Value.as_term ~loc v in
          as_eq_alpha (Jdg.mk_ty ctxv tv) >>= fun (tv,e1,e2) ->
          if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
          then
            as_signature_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) >>= fun xts ->
            Monad.lift Value.lookup_penv >>= fun penv ->
            let ctx = Context.join ~penv ~loc ctx ctxv in
            let hyps = Tt.assumptions_term ev in
            Monad.add_hyps hyps >>= fun () ->
            Monad.return (ctx,xts)
          else
            Monad.lift (Value.print_ty) >>= fun pty ->
            Error.typing ~loc:ev.Tt.loc
                "this expression should be a witness of equality between %t and a signature"
                (pty t)
      end

