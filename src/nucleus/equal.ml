(** Equality checking and weak-head-normal-forms *)

(** Notation for the monads bind *)

module AtomSet = Name.AtomSet

module Monad = struct
  type state = AtomSet.t

  let empty = AtomSet.empty

  type 'a t =
    { k : 'r. ('a -> state -> 'r Runtime.comp) -> state -> 'r Runtime.comp }

  let return x =
    { k = fun c s -> c x s }

  let (>>=) m f =
    { k = fun c s -> m.k (fun x s -> (f x).k c s) s }

  (* lift : 'a Runtime.comp -> 'a t *)
  let lift m =
    { k = fun c s -> Runtime.bind m (fun x -> c x s) }

  let modify f =
    { k = fun c s -> c () (f s) }

  let add_hyps hyps = modify (AtomSet.union hyps)

  let context_abstract ~loc ctx y t =
    lift Runtime.lookup_penv >>= fun penv ->
    let ctx = Context.abstract ~penv:penv.Runtime.base ~loc ctx y t in
    modify (fun hyps -> AtomSet.remove y hyps) >>= fun () ->
    return ctx

  let run m =
    m.k (fun x s -> Runtime.return (x,s)) empty
end

module Opt = struct
  type state = Monad.state

  type 'a opt =
    { k : 'r. ('a -> state -> 'r Runtime.comp) -> (state -> 'r Runtime.comp) -> state -> 'r Runtime.comp }

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
          Runtime.add_abstracting ~loc x j (fun ctx z -> (m ctx z).k (fun y s' -> (sk y s')) fk s) }

  let run m =
    m.k (fun x s -> Runtime.return (Some (x,s))) (fun _ -> Runtime.return None) AtomSet.empty
end

module Internals = struct

let (>>=) = Monad.(>>=)

let (>?=) = Opt.(>?=)

let (>!=) m f = (Opt.unfailing m) >?= f

(** Compare two types *)
let rec equal ctx ({Tt.loc=loc1;_} as e1) ({Tt.loc=loc2;_} as e2) t =
  if Tt.alpha_equal e1 e2
  then
    Opt.return ctx
  else
    Monad.lift (Predefined.operation_equal
        (Runtime.mk_term (Jdg.mk_term ctx e1 t))
        (Runtime.mk_term (Jdg.mk_term ctx e2 t))) >!= fun v ->
    let loc = loc1 in
    match Predefined.as_option ~loc v with
      | None -> Opt.fail
      | Some v ->
        let Jdg.Term (ctxeq,eq,teq) = Runtime.as_term ~loc v in
        Monad.lift Runtime.lookup_penv >!= fun penv ->
        let ctx = Context.join ~penv:penv.Runtime.base ~loc ctx ctxeq in
        Monad.add_hyps (Tt.assumptions_term eq) >!= fun () ->
        let tgoal = Tt.mk_eq_ty ~loc t e1 e2 in
        equal_ty ctx teq tgoal

and equal_ty ctx (Tt.Ty t1) (Tt.Ty t2) = equal ctx t1 t2 Tt.typ

(** Apply the appropriate congruence rule *)
let congruence ~loc ctx ({Tt.loc=loc1;_} as e1) ({Tt.loc=loc2;_} as e2) t =
  match e1.Tt.term, e2.Tt.term with

  | Tt.Atom x, Tt.Atom y ->
     if Name.eq_atom x y then Opt.return ctx
     else Opt.fail

  | Tt.Bound _, _ | _, Tt.Bound _ ->
     assert false

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

  | (Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Apply _ |
     Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _), _ ->
     Opt.fail


let extensionality ~loc ctx e1 e2 (Tt.Ty t') =
  match t'.Tt.term with
  | Tt.Prod ((x, a), b) ->
    Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a)
      (fun ctx y ->
      let yt = Tt.mk_atom ~loc y in
      let e1' = Tt.mk_apply ~loc e1 x a b yt in
      let e2' = Tt.mk_apply ~loc e2 x a b yt in
      let b' = Tt.unabstract_ty [y] b in
      equal ctx e1' e2' b' >?= fun ctx ->
      Monad.context_abstract ~loc ctx y a >!= fun ctx ->
      Opt.return ctx)

  | Tt.Eq _ -> Opt.return ctx

  | Tt.Type | Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Apply _ | Tt.Refl _ ->
    Opt.fail

  | Tt.Bound _ ->
     assert false



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
           | Tt.Refl _ -> Opt.fail
           | Tt.Bound _ -> assert false              
     end

  | Tt.Constant _
  | Tt.Lambda _
  | Tt.Prod _
  | Tt.Atom _
  | Tt.Type
  | Tt.Eq _
  | Tt.Refl _ -> Opt.fail
  | Tt.Bound _ -> assert false


let as_eq_alpha (Jdg.Ty (_, (Tt.Ty {Tt.term=t';_}))) =
  match t' with
    | Tt.Eq (t, e1, e2) -> Some (t, e1, e2)
    | _ -> None

let as_eq (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Eq (t, e1, e2) -> Monad.return (ctx, t, e1, e2)
    | _ ->
      Monad.lift (Predefined.operation_as_eq (Runtime.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Predefined.as_option ~loc v with
        | None ->
          Runtime.(error ~loc (EqualityTypeExpected jt))
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Runtime.as_term ~loc v in
          begin
            let j_tv = Jdg.mk_ty ctxv tv in
            match as_eq_alpha j_tv with
            | None ->
               Runtime.(error ~loc (InvalidAsEquality j_tv))
            | Some (tv, e1, e2) ->
               if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
               then
                 let j_e2 = Jdg.mk_ty ctxv (Tt.ty e2) in
                 begin
                   match as_eq_alpha j_e2 with
                   | None -> 
                      Runtime.(error ~loc (InvalidAsEquality j_tv))

                   | Some (t,e1,e2) ->
                      Monad.lift Runtime.lookup_penv >>= fun penv ->
                      let ctx = Context.join ~penv:penv.Runtime.base ~loc ctx ctxv in
                      let hyps = Tt.assumptions_term ev in
                      Monad.add_hyps hyps >>= fun () ->
                      Monad.return (ctx,t,e1,e2)
                 end
               else
                 Runtime.(error ~loc (InvalidAsEquality j_tv))
          end
      end

let as_prod_alpha (Jdg.Ty (_, (Tt.Ty {Tt.term=t';_}))) =
  match t' with
    | Tt.Prod (xts,t) -> Some (xts,t)
    | _ -> None

let as_prod (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Prod (xts,t) -> Monad.return (ctx, (xts,t))
    | _ ->
      Monad.lift (Predefined.operation_as_prod (Runtime.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Predefined.as_option ~loc v with
        | None -> Runtime.(error ~loc (ProductExpected jt))
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Runtime.as_term ~loc v in
          let j_tv = Jdg.mk_ty ctxv tv in
          begin
            match as_eq_alpha j_tv with
            | None -> Runtime.(error ~loc (InvalidAsProduct j_tv))
            | Some (tv,e1,e2) ->
               if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
               then
                 begin
                   match as_prod_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) with
                   | None -> Runtime.(error ~loc (InvalidAsProduct j_tv))
                   | Some (xts,t) ->
                      Monad.lift Runtime.lookup_penv >>= fun penv ->
                      let ctx = Context.join ~penv:penv.Runtime.base ~loc ctx ctxv in
                      let hyps = Tt.assumptions_term ev in
                      Monad.add_hyps hyps >>= fun () ->
                      Monad.return (ctx,(xts,t))
                 end
               else
                 Runtime.(error ~loc (InvalidAsProduct j_tv))
          end
      end

end

(** Expose without the monad stuff *)

type 'a witness = ('a * AtomSet.t) Runtime.comp

type 'a opt = ('a * AtomSet.t) option Runtime.comp

let equal ctx e1 e2 t = Opt.run (Internals.equal ctx e1 e2 t)

let equal_ty ctx t1 t2 = Opt.run (Internals.equal_ty ctx t1 t2)

let reduction_step ctx e = Opt.run (Internals.reduction_step ctx e)

let congruence ~loc ctx e1 e2 t = Opt.run (Internals.congruence ~loc ctx e1 e2 t)

let extensionality ~loc ctx e1 e2 t = Opt.run (Internals.extensionality ~loc ctx e1 e2 t)

let as_eq j = Monad.run (Internals.as_eq j)

let as_prod j = Monad.run (Internals.as_prod j)

