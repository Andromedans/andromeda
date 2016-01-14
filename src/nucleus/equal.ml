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

  let unfold (m : 'a opt) : 'a option Monad.t =
    { Monad.k = fun c s -> m.k (fun x s' -> c (Some x) s') (fun s' -> c None s') s }

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

let (>?>=) m f = (Opt.unfold m) >>= f

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
    Monad.lift (Value.perform_equal (Value.mk_term (ctx,e1,t)) (Value.mk_term (ctx,e2,t))) >!= fun v ->
    let loc = loc1 in
    match Value.as_option ~loc v with
      | Some v ->
        let (ctxeq,eq,teq) = Value.as_term ~loc v in
        let ctx = Context.join ~loc ctx ctxeq in
        Monad.add_hyps (Tt.assumptions_term eq) >!= fun () ->
        let tgoal = Tt.mk_eq_ty ~loc t e1 e2 in
        equal_ty ctx teq tgoal
      | None -> Opt.fail

and equal_ty ctx (Tt.Ty t1) (Tt.Ty t2) = equal ctx t1 t2 Tt.typ

(** Let [xuus] be the list [(x1,(u1,u1')); ...; (xn,(un,un'))] where
    [ui]  is well-formed in the context [x1:u1 , ..., x{i-1}:u{i-1} ] and
    [ui'] is well-formed in the context [x1:u1', ..., x{i-1}:u{i-1}'] and
    [v]  is well-formed in the context [x1:u1, ..., xn:un] and
    [v'] is well-formed in the context [x1:u1',..., xn:un'].
    We verify that the [ui] are equal to [ui'] and that [v] is equal to [v]. *)
let equal_abstracted_ty ctx (xuus : (Name.ident * (Tt.ty * Tt.ty)) list) v v' =
  (* As we descend into the contexts we carry around a list of variables
     [ys] with which we unabstract the bound variables. *)
  let rec eq ctx ys ys' ts =
    function
     | [] ->
        (* XXX think whether the order of [ys] is correct everywhere *)
        let v = Tt.unabstract_ty ys v
        and v' = Tt.instantiate_ty ys' v' in
        equal_ty ctx v v' >?= fun ctx ->
        Monad.context_abstract ~loc:Location.unknown ctx ys ts >!= fun ctx ->
        Opt.return ctx
     | (x,(u,u'))::xuus ->
        let u  = Tt.unabstract_ty ys u
        and u' = Tt.instantiate_ty ys' u' in
        Opt.locally (equal_ty ctx u u') >?= fun (ctx,hypsu) ->
        let ju = Judgement.mk_ty ctx u in
        Opt.add_free ~loc:Location.unknown x ju (fun ctx y ->
        let Tt.Ty {Tt.loc=loc;_} = u' in
        let y' = Tt.mention_atoms hypsu (Tt.mk_atom ~loc y) in
        eq ctx (y :: ys) (y' :: ys') (u :: ts) xuus)
  in
  eq ctx [] [] [] xuus


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
        let jx = Judgement.mk_ty ctx t1 in
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
let congruence ctx ({Tt.term=e1';loc=loc1;_} as e1) ({Tt.term=e2';loc=loc2;_} as e2) t =
  Print.debug "congruence of %t and %t"
              (Tt.print_term [] e1)
              (Tt.print_term [] e2) ;
  match e1', e2' with

  | Tt.Atom x, Tt.Atom y ->
     if Name.eq_atom x y then Opt.return ctx
     else Opt.fail

  | Tt.Bound _, _ | _, Tt.Bound _ ->
     Error.impossible ~loc:loc1 "deBruijn encountered in congruence"

  | Tt.Constant (x1, es1), Tt.Constant (x2, es2) ->
     if not @@ Name.eq_ident x1 x2
     then Opt.fail
     else
       begin Monad.lift (Value.lookup_constant x1) >!= function
       | Some ytsu -> Opt.return ytsu
       | None -> Error.impossible ~loc:loc1 "unknown constant %t in congruence"
                                            (Name.print_ident x1)
       end >?= fun (yts,_) ->
       let rec fold ctx es' hyps yts es1 es2 =
         match yts, es1, es2 with
         | [], [], [] -> Opt.return ctx

         | (y,(_,t))::yts, e1::es1, e2::es2 ->
            let e2 = Tt.mention_atoms hyps e2 in
            let t = Tt.instantiate_ty es' t in
            Opt.locally (equal ctx e1 e2 t) >?= fun (ctx,hyps') ->
            fold ctx (e1 :: es') (AtomSet.union hyps hyps') yts es1 es2

         | _, _, _ ->
            Error.impossible ~loc:loc1 "primitive application equality (%d, %d, %d)"
              (List.length yts)
              (List.length es1)
              (List.length es2)
       in
       fold ctx [] AtomSet.empty yts es1 es2

  | Tt.Lambda (xus, (e1, t1)), Tt.Lambda (xvs, (e2, t2)) ->
     (** [ys] is the list of atoms from the lhs.
         [ys'] is the same list, but as terms with appropriate assumptions to give them the types of the rhs.
         Note that [ts] is only used to abstract the context, so there's no need for a version with rhs assumptions. *)
     let rec zip ys ys' ts ctx = function
       | (x, u) :: xus, (_, u') :: xvs ->
          let u  = Tt.unabstract_ty ys u
          and u' = Tt.instantiate_ty ys' u' in
          Opt.locally (equal_ty ctx u u') >?= fun (ctx,hypsu) ->
          let ju = Judgement.mk_ty ctx u in
          Opt.add_abstracting ~loc:Location.unknown x ju (fun ctx y ->
          let Tt.Ty {Tt.loc=loc;_} = u' in
          let y' = Tt.mention_atoms hypsu (Tt.mk_atom ~loc y) in
          (* XXX optimize list append *)
          zip (ys @ [y]) (ys' @ [y']) (ts @ [u]) ctx (xus, xvs))

       | ([] as xus), xvs | xus, ([] as xvs) ->
          let t1' = Tt.mk_prod_ty ~loc:Location.unknown xus t1
          and t2' = Tt.mk_prod_ty ~loc:Location.unknown xvs t2 in
          let t1' = Tt.unabstract_ty ys t1'
          and t2' = Tt.instantiate_ty ys' t2' in
          Opt.locally (equal_ty ctx t1' t2') >?= fun (ctx,hypst) ->
          let e1 = Tt.mk_lambda ~loc:(e1.Tt.loc) xus e1 t1
          and e2 = Tt.mk_lambda ~loc:(e2.Tt.loc) xvs e2 t2 in
          let e1 = Tt.unabstract ys e1
          and e2 = Tt.instantiate ys' e2 in
          let e2 = Tt.mention_atoms hypst e2 in
          equal ctx e1 e2 t1' >?= fun ctx ->
          Monad.context_abstract ~loc:Location.unknown ctx ys ts >!= fun ctx ->
          Opt.return ctx
     in
     zip [] [] [] ctx (xus, xvs)

  | Tt.Spine (h1, (xts1,out1), es1), Tt.Spine (h2, (xts2,out2), es2) ->
    (* first get the ends of the spines *)
    let pop_end l =
      let rec pop_end pre = function
        | [] -> Error.impossible ~loc:Location.unknown "invalid spine in congruence"
        | [x] -> x,List.rev pre
        | x::tl -> pop_end (x::pre) tl
      in
      pop_end [] l
    in
    let e1,es1 = pop_end es1
    and e2,es2 = pop_end es2
    and (x1,t1),xts1 = pop_end xts1
    and (x2,t2),xts2 = pop_end xts2 in
    (* type of the last argument *)
    let tinst1 = Tt.instantiate_ty (List.rev es1) t1
    and tinst2 = Tt.instantiate_ty (List.rev es2) t2 in
    Opt.locally (equal_ty ctx tinst1 tinst2) >?= fun (ctx,hypst) ->
    (* output type abstracted for last argument *)
    Opt.locally (
      Opt.add_abstracting ~loc:loc1 x1 (ctx,tinst1) (fun ctx y ->
      let tey1 = Tt.mk_atom ~loc:loc1 y in
      let tey2 = Tt.mention_atoms hypst tey1 in
      let out_inst1 = Tt.instantiate_ty (tey1::(List.rev es1)) out1
      and out_inst2 = Tt.instantiate_ty (tey2::(List.rev es2)) out2 in
      equal_ty ctx out_inst1 out_inst2 >?= fun ctx ->
      Opt.unfailing (Monad.context_abstract ~loc:Location.unknown ctx [y] [tinst1])) >?= fun ctx ->
      Opt.return ctx
      ) >?= fun (ctx,hypso) ->
    (* last argument *)
    equal ctx e1 (Tt.mention_atoms hypst e2) tinst1 >?= fun ctx ->
    (* abstracted output type of the head *)
    let th1 = Tt.mk_prod_ty ~loc:loc1 [(x1,t1)] out1
    and th2 = Tt.mk_prod_ty ~loc:loc2 [(x2,t2)] out2 in
    (* head *)
    let h1 = Tt.mk_spine ~loc:loc1 h1 xts1 th1 es1
    and h2 = Tt.mk_spine ~loc:loc2 h2 xts2 th2 es2 in
    (* type of the head *)
    let th = Tt.instantiate_ty (List.rev es1) th1 in (*NB: equal to the same for rhs by hypst and hypso *)
    let h2 = Tt.mention_atoms (AtomSet.union hypst hypso) h2 in
    equal ctx h1 h2 th

  | Tt.Type, Tt.Type -> Opt.return ctx

  | Tt.Prod (xus, t1), Tt.Prod (xvs, t2) ->
     let rec zip xuvs = function
       | (x, u) :: xus, (_, v) :: xvs ->
          zip ((x, (u, v)) :: xuvs) (xus, xvs)
       | ([] as xus), xvs | xus, ([] as xvs) ->
          let xuvs = List.rev xuvs in
          let t1 = Tt.mk_prod_ty ~loc:loc1 xus t1
          and t2 = Tt.mk_prod_ty ~loc:loc2 xvs t2 in
          equal_abstracted_ty ctx xuvs t1 t2
     in
     zip [] (xus, xvs)

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

  | (Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Spine _ |
     Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _ |
     Tt.Signature _ | Tt.Structure _ | Tt.Projection _), _ ->
     Opt.fail

(** Beta reduction of [Lambda (xus, (e, u))] applied to arguments [es],
    where [(yvs, t)] is the typing annotation for the application.
    Returns the resulting expression. *)
let beta_reduce ~loc ctx xus e u yvs t es =
  let rec split xuvs es' xus yvs es =
    match xus, yvs, es with
    | ([], _, _) | (_, [], []) -> xuvs, es', xus, yvs, es
    | (x,u)::xus, (_,v)::yvs, e::es -> split (xuvs @ [(x,(u,v))]) (e::es') xus yvs es
    | (_, [], _::_) | (_, _::_, []) ->
      Error.impossible ~loc "Equal.beta_reduce encountered an invalid spine"
  in
  let xuvs, es', xus, yvs, es = split [] [] xus yvs es in

  (* [xuvs] is a list of triples [(x,u,v)] ready to be plugged into [equal_abstraction] *)
  (* [es'] is the list of arguments that we are plugging in (reverse order from [es]) *)
  (* [xus] is the list of leftover abstraction arguments *)
  (* [yvs, es] is the list of leftover arguments *)
  (* XXX: optimization -- use the fact that one or both of [xus] and [yevs, es] are empty. *)
  let u' = Tt.mk_prod_ty ~loc xus u
  and t' = Tt.mk_prod_ty ~loc yvs t in
  Opt.locally (equal_abstracted_ty ctx xuvs u' t') >?= fun (ctx, hyps) ->
   (* XXX TODO we put hyps everywhere, we could instead be more precise *)
   let es' = List.map (Tt.mention_atoms hyps) es' in
   let xus, (e, u) = Tt.instantiate_ty_abstraction Tt.instantiate_term_ty es' (xus, (e, u))
   and yvs, t = Tt.instantiate_ty_abstraction Tt.instantiate_ty es' (yvs, t) in
   let e = Tt.mk_lambda ~loc xus e u in
   let e = Tt.mk_spine ~loc e yvs t es in
   let e = Tt.mention_atoms hyps e in
   Opt.return (ctx, e)

(** Reduction of [{xtes}.p] at type [{xts}] *)
let projection_reduce ~loc ctx xts p xtes =
  equal_signature ~loc ctx xts (List.map (fun (l,x,t,_) -> l,x,t) xtes) >?= fun ctx ->
  let te = Tt.field_value ~loc xtes p in
  Opt.return (ctx,te)

let reduce_step ctx {Tt.term=e'; assumptions; loc} =
  match e' with
  | Tt.Spine (e, ([], _), _) -> Error.impossible ~loc "empty spine in reduce_step"
  | Tt.Lambda ([], (e, _)) -> Error.impossible ~loc "empty lambda in reduce_step"
  | Tt.Prod ([], Tt.Ty e) -> Error.impossible ~loc "empty product in reduce_step"
  | Tt.Spine (e1, (((_::_) as xts), t), ([_] as es)) ->
     begin match e1.Tt.term with
           | Tt.Lambda (xus, (e', u)) ->
              beta_reduce ~loc ctx xus e' u xts t es >?= fun (ctx, e) ->
              Opt.return (ctx, Tt.mention assumptions e)
           | Tt.Atom _
           | Tt.Constant _
           | Tt.Spine _
           | Tt.Type
           | Tt.Prod _
           | Tt.Eq _
           | Tt.Refl _
           | Tt.Signature _
           | Tt.Structure _
           | Tt.Projection _ -> Opt.fail
           | Tt.Bound _ ->
              Error.impossible ~loc "de Bruijn encountered in a spine head in reduce"
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
       | Tt.Spine _
       | Tt.Type
       | Tt.Prod _
       | Tt.Eq _
       | Tt.Refl _
       | Tt.Signature _
       | Tt.Projection _ -> Opt.fail
       | Tt.Bound _ ->
          Error.impossible ~loc "de Bruijn encountered in a projection head in reduce"
     end

  | Tt.Spine (_, ((_::_), _), ([]|(_::_::_)))
  | Tt.Constant _
  | Tt.Lambda (_ :: _, _)
  | Tt.Prod (_ :: _, _)
  | Tt.Atom _
  | Tt.Type
  | Tt.Eq _
  | Tt.Refl _
  | Tt.Signature _
  | Tt.Structure _ -> Opt.fail
  | Tt.Bound _ ->
     Error.impossible ~loc "de Bruijn encountered in reduce"


let rec as_form : type a. (_ -> a Monad.t) -> _ -> _ -> _ -> a Monad.t =
  fun triviality thing (ctx, Tt.Ty ({Tt.term=t';loc;_} as t)) v ->
  begin match Value.as_option ~loc v with
    | None ->  Error.typing ~loc "this expression should be %s, found@ %t" thing
                    (Tt.print_term [] t)
    | Some v ->
      let (ctxv,ev,tv) = Value.as_term ~loc v in
      as_eq (ctxv, tv) >>= fun (ctxv,tv,e1,e2) ->
      (Opt.locally (equal_ty ctxv tv Tt.typ) >?= fun (ctx,hypst) ->
        let t1 = Tt.mention_atoms hypst e1
        and t2 = Tt.mention_atoms hypst e2 in
        let ctx = Context.join ~loc ctx ctxv in
        equal ctx t t1 Tt.typ >?= fun ctx ->
        Monad.add_hyps (Tt.assumptions_term ev) >!= fun () ->
        Opt.return (ctx,t2)
      ) >?>= begin function
        | None ->
            Monad.lift (Value.print_value) >>= fun pval ->
            Monad.lift (Value.print_term) >>= fun pte ->
            Error.typing ~loc:(ev.Tt.loc)
                  "this expression %t should be a witness of equality between %t and %s"
                  (pval v) (pte t) thing
        | Some (ctx,t) ->
          triviality (ctx, Tt.ty t)
      end
  end

and as_eq ((ctx, Tt.Ty {Tt.term=t';_}) as jt) =
  match t' with
    | Tt.Eq (t, e1, e2) -> Monad.return (ctx, t, e1, e2)
    | _ ->
      Monad.lift (Value.perform_as_eq (Value.mk_term (Judgement.term_of_ty jt))) >>=
      as_form as_eq "an equality type" jt

let rec as_prod ((ctx, Tt.Ty {Tt.term=t';_}) as jt) =
  match t' with
    | Tt.Prod (xts,t) -> Monad.return (ctx, (xts,t))
    | _ ->
      Monad.lift (Value.perform_as_prod (Value.mk_term (Judgement.term_of_ty jt))) >>=
      as_form as_prod "a product type" jt

let rec as_signature ((ctx, Tt.Ty {Tt.term=t';_}) as jt) =
  match t' with
    | Tt.Signature xts -> Monad.return (ctx, xts)
    | _ ->
      Monad.lift (Value.perform_as_signature (Value.mk_term (Judgement.term_of_ty jt))) >>=
      as_form as_signature "a signature type" jt

