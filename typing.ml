(** Type checking and synthesis. *)

open Syntax
open Context

(** [equal_at ctx e1 e2 t] compares expressions [e1] and [e2] at kind [t]. It is assumed
    that [t] is a valid kind. It is also assumed that [e1] and [e2] have kind [t]. *)
let rec equal_at ctx e1 e2 t =
  let t = Norm.whnf ctx t in
    match fst t with
      | Pi (x, t1, t2) ->
        let e1' = mk_app (shift 1 e1) (mk_var 0) in
        let e2' = mk_app (shift 1 e2) (mk_var 0) in
          equal_at (add_parameter x t1 ctx) e1' e2' t2
      | EqJdg _ -> equal ctx e1 e2
      | TyJdg _ -> equal ctx e1 e2
      | Kind _ -> equal_kind ctx e1 e2
      | Var _ | App _ -> equal ctx e1 e2
      | TyWtn _ | EqWtn _ | Lambda _ | Subst _ | Ascribe _ ->
        Error.runtime ~loc:(snd t) "internal error, compare at non-kind"

and equal ctx e1 e2 =
  let e1 = Norm.whnf ctx e1 in
  let e2 = Norm.whnf ctx e2 in
    match fst e1, fst e2 with
      | Kind m, Kind n -> m = n
      | EqJdg (e1, e2, t), EqJdg (e1', e2', t') ->
        equal_kind ctx t t' &&
        equal_at ctx e1 e1' t &&
        equal_at ctx e2 e2' t
      | EqWtn (e1, e2, t), EqWtn (e1', e2', t') ->
        equal_kind ctx t t' &&
        equal_at ctx e1 e1' t &&
        equal_at ctx e2 e2' t
      | TyJdg (e1, t1), TyJdg (e2, t2) ->
        equal_kind ctx t1 t2 &&
        equal_at ctx e1 e2 t1
      | TyWtn (e1, t1), TyWtn (e2, t2) ->
        equal_kind ctx t1 t2 &&
        equal_at ctx e1 e2 t1
      | Pi (x, t1, t2), Pi (_, s1, s2) ->
        equal_kind ctx t1 s1 &&
        equal_kind (add_parameter x t1 ctx) t2 s2
      | Var _, Var _
      | App _, App _ -> None <> equal_spine ctx e1 e2
      | (Var _ | Pi _ | Lambda _ | App _ | Subst _ |
         Ascribe _ | Kind _ | EqWtn _ | TyWtn _ | EqJdg _ | TyJdg _), _ -> false

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
    | (Var _ | Pi _ | Lambda _ | App _ |
        Subst _ | Ascribe _ | Kind _ | EqWtn _ | TyWtn _ | EqJdg _ | TyJdg _), _ -> None

(** [t1] and [t2] must be valid kinds. *)
and equal_kind ctx t1 t2 = equal ctx t1 t2

(** [infer ctx e] infers the kind of expression [e] in context [ctx]. *)
let rec infer ctx (e, loc) =
  match e with

    | Var k -> lookup_ty k ctx

    | Pi (x, t1, t2) ->
      let n1 = infer_level ctx t1 in
      let n2 = infer_level (add_parameter x t1 ctx) t2 in
      let n = Common.max_level n1 n2 in
        mk_kind n

    | Subst (s, e) -> infer ctx (subst s e)

    | App (e1, e2) ->
      let (x, t1, t2) = infer_pi ctx e1 in
        check ctx e2 t1 ;
        mk_subst (Dot (e2, idsubst)) t2

    | Lambda (x, None, _) -> Error.typing ~loc "cannot infer the kind of %s" x

    | Lambda (x, Some t1, e) ->
      check_kind ctx t1 ;
      let t2 = infer (add_parameter x t1 ctx) e in
        mk_pi x t1 t2

    | Ascribe (e, t) ->
      check ctx e t ;
      t

    | Kind m -> mk_kind (Common.succ_level m)

    | TyWtn (e, t) -> mk_tyjdg e t

    | EqWtn (e1, e2, t) -> mk_eqwtn e1 e2 t

    | EqJdg (e1, e2, t) ->
      let n = infer_level ctx t in
        check ctx e1 t ;
        check ctx e2 t ;
        mk_kind (Common.succ_level n)

    | TyJdg (e, t) ->
      let n = infer_level ctx t in
        check ctx e t ;
        mk_kind (Common.succ_level n)


and check ctx ((e', loc) as e) t =
  check_kind ctx t ;
  match e' with
    | Subst (s, e) -> check ctx (subst s e) t (* XXX avoid rechecking t *)
    | Lambda (x, None, e) ->
      (match fst (Norm.whnf ctx t) with
        | Pi (x, t1, t2) -> check (add_parameter x t1 ctx) e t2
        | _ -> Error.typing ~loc "this expression is a function but should have kind@ %t"
          (Print.expr ctx.names t))
    | Var _ | Lambda (_, Some _, _) | Pi _ | App _ |
        Ascribe _ | Kind _ | TyJdg _ | EqJdg _ | TyWtn _ | EqWtn _ ->
      let t' = infer ctx e in
        if not (equal_kind ctx t' t) then
          Error.typing ~loc:(snd e) "this expression has kind %t@ but it should have kind %t"
            (Print.expr ctx.names t') (Print.expr ctx.names t)

(* Check that the given expression is a sort and return the level at which it resides. *)
and infer_level ctx (e',loc) =
  match e' with
    | Var k ->
      let t = lookup_ty k ctx in
      (match fst (Norm.whnf ctx t) with
        | Kind n -> n
        | _ -> Error.typing ~loc "this expression has kind %t@ but should be a kind" (Print.expr ctx.names t))
    | Subst (s, e) -> infer_level ctx (subst s e)
    | Lambda _ -> Error.typing ~loc "this expression is a function but should be a kind"
    | Pi (x, t1, t2) ->
      let u1 = infer_level ctx t1 in
      let u2 = infer_level (add_parameter x t1 ctx) t2 in
        Common.max_level u1 u2
    | App (e1, e2) ->
      let (x, t1, t2) = infer_pi ctx e1 in
        check ctx e2 t1 ;
        infer_kind ctx (mk_subst (Dot (e2, idsubst)) t2)
    | Ascribe (e1, e2) ->
      check ctx e1 e2 ;
      infer_level ctx e1
    | Kind n -> Common.succ_level n
    | EqWtn _ -> Error.typing ~loc "this expression is an equality witness but should be a kind"
    | TyWtn _ -> Error.typing ~loc "this expression is a typing witness but should be a kind"
    | EqJdg (e1, e2, t) ->
      let n = infer_level ctx t in
      check ctx e1 t ;
      check ctx e2 t ;
      n
    | TyJdg (e, t) ->
      let n = infer_level ctx t in
      check ctx e t ;
      n

and check_kind ctx e = ignore (infer_level ctx e)

and infer_kind ctx e =
  match fst (Norm.whnf ctx e) with
    | Kind n -> n
    | Subst _ | Ascribe _ -> assert false
    | Pi _ | Var _ | App _ | EqJdg _ | TyJdg _ | TyWtn _ | EqWtn _ | Lambda _ ->
        Error.typing ~loc:(snd e) "this expression is a %t@ but it should be a kind" (Print.expr ctx.names e)

and infer_pi ctx e =
  let t = infer ctx e in
    match fst (Norm.whnf ctx t) with
      | Pi (x, t1, t2) -> (x, t1, t2)
      | Subst _ | Ascribe _ -> assert false
      | Var _ | App _ | Kind _ | EqJdg _ | TyJdg _ | TyWtn _ | EqWtn _ | Lambda _ ->
        Error.typing ~loc:(snd e) "this expression has kind %t@ but it should be a function" (Print.expr ctx.names t)
