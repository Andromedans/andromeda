(** Type inference. *)

open Syntax
open Context

(** [equal_at ctx e1 e2 t] compares expressions [e1] and [e2] at type [t]. It is assumed
    that [t] is a valid type. It is not assumed that [e1] and [e2] have type [t]. *)
let rec equal_at ctx e1 e2 t =
  let t = Norm.whnf ctx t in
    match fst t with
      | Pi (x, t1, t2) ->
        equal_at (add_parameter x t1 ctx) (mk_app e1 (mk_var 0)) (mk_app e2 (mk_var 0)) t2
      | Universe u ->
        (match equal_ty ctx e1 e2 with
          | Some u' -> u = u'
          | None -> false)
      | App _ ->
        (match equal ctx e1 e2 with
          | None -> false
          | Some t' ->
            (match equal_ty ctx t t' with
              | None -> false
              | Some _ -> true))
      | Lambda _ | Var _ | Subst _ | Ascribe _ -> assert false

and equal ctx e1 e2 =
  let e1 = Norm.whnf ctx e1 in
  let e2 = Norm.whnf ctx e2 in
    match fst e1, fst e2 with
      | Universe u1, Universe u2 when u1 = u2 -> Some (mk_universe (u1 + 1))
      | Pi (x, t1, t2), Pi (_, s1, s2) ->
        (match equal_ty ctx t1 s1 with
          | None -> None
          | Some u1 ->
            (match equal_ty (add_parameter x t1 ctx) t1 s2 with
              | None -> None
              | Some u2 -> Some (mk_universe (max u1 u2))))
      | Var _, Var _
      | App _, App _ -> equal_spine ctx e1 e2
      | (Var _ | Universe _ | Pi _ | Lambda _ | App _ | Subst _ | Ascribe _), _ -> None

and equal_spine ctx e1 e2 =
  match fst e1, fst e2 with
    | Var k1, Var k2 ->
      if k1 = k2
      then Some (lookup_ty k2 ctx)
      else None

    | App (a1, a2), App (b1, b2) ->
      (match equal_spine ctx a1 b1 with
        | None -> None
        | Some t ->
          (match fst (Norm.whnf ctx t) with
            | Pi (x, u1, u2) ->
              if equal_at ctx a2 b2 u1
              then Some (mk_subst (Dot (a2, idsubst)) u2)
              else None
            | _ -> None))
    | (Var _ | Universe _ | Pi _ | Lambda _ | App _ | Subst _ | Ascribe _), _ -> None

and equal_ty ctx t1 t2 =
  match equal ctx t1 t2 with
    | Some t ->
      (match fst (Norm.whnf ctx t) with
        | Universe u -> Some u
        | _ -> None)
    | None -> None

(** [infer ctx e] infers the type of expression [e] in context [ctx]. *)
let rec infer ctx (e, loc) =
  match e with
    | Var k -> lookup_ty k ctx
    | Universe u -> mk_universe (u + 1)
    | Pi (x, t1, t2) ->
      let u1 = infer_universe ctx t1 in
      let u2 = infer_universe (add_parameter x t1 ctx) t2 in
        mk_universe (max u1 u2)
    | Subst (s, e) -> infer ctx (Syntax.subst s e)
    | App (e1, e2) ->
      let (x, s, t) = infer_pi ctx e1 in
        check ctx e2 s ;
        mk_subst (Dot (e2, idsubst)) t
    | Lambda (x, t, e) ->
      let t' = infer (add_parameter x t ctx) e in
        mk_pi x t t'
    | Ascribe (e, t) ->
      check ctx e t ;
      let _ = infer_universe ctx t in
        t

(** [check ctx e t] checks that [e] has type [t]. It is assumed that [t] is a valid type. *)
and check ctx ((e', loc) as e) t =
  match e' with
    | Var _ | Pi _ | App _ | Universe _ ->
      let t' = infer ctx e in
        (match equal_ty ctx t t' with
          | Some _ -> ()
          | None -> Error.typing ~loc "this expression should have type@ %t." (Print.expr ctx.names t))
    | Subst (s, e) -> check ctx (Syntax.subst s e) t
    | Lambda (x, t', e) ->
      (match fst (Norm.whnf ctx t) with
        | Pi (x, t1, t2) ->
          (match equal_ty ctx t' t1 with
            | Some _ -> check (add_parameter x t1 ctx) e t2
            | None ->
              Error.typing ~loc "this function should have domain@ %t@ but it has domain@ %t."
                (Print.expr ctx.names t1) (Print.expr ctx.names t'))
        | _ -> 
          Error.typing ~loc "this expression should have type@ %t@ but it is a function" (Print.expr ctx.names t)
      )
    | Ascribe (e, t') -> 
      (match equal_ty ctx t' t with
        | Some _ -> check ctx e t'
        | None -> Error.typing ~loc:(snd t') "this expression should be type@ %t@" (Print.expr ctx.names t))

(** [infer_universe ctx t] infers the universe level of type [t] in context [ctx]. *)
and infer_universe ctx t =
  let u = infer ctx t in
    match fst (Norm.whnf ctx u) with
      | Universe u -> u
      | Subst _ | Ascribe _ -> assert false
      | App _ | Var _ | Pi _ | Lambda _ ->
        Error.typing ~loc:(snd t) "this expression has type@ %t@ but it should be a universe" (Print.expr ctx.names u)

and infer_pi ctx e =
  let t = infer ctx e in
    match fst (Norm.whnf ctx t) with
      | Pi (x, t1, t2) -> (x, t1, t2)
      | Subst _ | Ascribe _ -> assert false
      | Var _ | App _ | Universe _ | Lambda _ ->
        Error.typing ~loc:(snd e) "this expression has type@ %t@ but it should be a function" (Print.expr ctx.names t)
