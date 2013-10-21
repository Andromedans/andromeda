(** Type inference. *)

open Syntax
open Context

type size = Small | Large

let max_size u1 u2 =
  match u1 with
    | Small -> u2
    | Large -> Large

(** [equal_at ctx e1 e2 t] compares expressions [e1] and [e2] at sort [t]. It is assumed
    that [t] is a valid sort. It is also assumed that [e1] and [e2] have sort [t]. *)
let rec equal_at ctx e1 e2 t =
  let t = Norm.whnf ctx t in
    match fst t with
      | Pi (x, t1, t2) ->
        let e1' = mk_app (shift 1 e1) (mk_var 0) in
        let e2' = mk_app (shift 1 e2) (mk_var 0) in
          equal_at (add_parameter x t1 ctx) e1' e2' t2
      | Type | Sort -> equal_sort ctx e1 e2
      | Var _ | App _ -> equal ctx e1 e2
      | Lambda _ | Subst _ | Ascribe _ ->
        Error.runtime ~loc:(snd t) "internal error, compare at non-sort"

and equal ctx e1 e2 =
  let e1 = Norm.whnf ctx e1 in
  let e2 = Norm.whnf ctx e2 in
    match fst e1, fst e2 with
      | Type, Type -> true
      | Sort, Sort -> true
      | Pi (x, t1, t2), Pi (_, s1, s2) ->
        equal_sort ctx t1 s1 &&
        equal_sort (add_parameter x t1 ctx) t2 s2
      | Var _, Var _
      | App _, App _ -> None <> equal_spine ctx e1 e2
      | (Var _ | Pi _ | Lambda _ | App _ | Subst _ | Ascribe _ | Type | Sort), _ -> false

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
    | (Var _ | Pi _ | Lambda _ | App _ | Subst _ | Ascribe _ | Type | Sort), _ -> None

(** [t1] and [t2] must be valid sorts. *)
and equal_sort ctx t1 t2 = equal ctx t1 t2

(** [infer ctx e] infers the sort of expression [e] in context [ctx]. *)
let rec infer ctx (e, loc) =
  match e with

    | Var k -> lookup_ty k ctx

    | Pi (x, t1, t2) ->
      let u1 = check_sort ctx t1 in
      let u2 = check_sort (add_parameter x t1 ctx) t2 in
        (match max_size u1 u2 with
          | Small -> mk_type
          | Large -> mk_kind)

    | Subst (s, e) -> infer ctx (subst s e)

    | App (e1, e2) ->
      let (x, t1, t2) = infer_pi ctx e1 in
        check ctx e2 t1 ;
        mk_subst (Dot (e2, idsubst)) t2

    | Lambda (x, None, _) -> Error.typing ~loc "cannot infer the sort of %s" x

    | Lambda (x, Some t1, e) ->
      ignore (check_sort ctx t1) ;
      let t2 = infer (add_parameter x t1 ctx) e in
        mk_pi x t1 t2

    | Ascribe (e, t) ->
      check ctx e t ;
      t

    | Type -> mk_kind

    | Sort -> Error.typing ~loc "sorry, you cannot use Sort as a sort"


and check ctx ((e', loc) as e) t =
  ignore (check_sort ctx t) ;
  match e' with
    | Subst (s, e) -> check ctx (subst s e) t (* XXX avoid rechecking t *)
    | Lambda (x, None, e) ->
      (match fst (Norm.whnf ctx t) with
        | Pi (x, t1, t2) -> check (add_parameter x t1 ctx) e t2
        | _ -> Error.typing ~loc "this expression is a function but should have sort@ %t"
          (Print.expr ctx.names t))
    | Sort -> Error.typing ~loc "Sort does not have sort %t" (Print.expr ctx.names t)
    | Var _ | Lambda (_, Some _, _) | Pi _ | App _ | Ascribe _ | Type ->
      let t' = infer ctx e in
        if not (equal_sort ctx t' t) then
          Error.typing ~loc:(snd e) "this expression has sort %t@ but it should have sort %t"
            (Print.expr ctx.names t') (Print.expr ctx.names t)

(* Returns [Small] if the sort is small and [Large] otherwise. *)
and check_sort ctx (e',loc) =
  match e' with
    | Var k ->
      let t = lookup_ty k ctx in
      (match fst (Norm.whnf ctx t) with
        | Type -> Small
        | Sort -> Large
        | _ -> Error.typing ~loc "this expression has sort %t@ but should be a sort" (Print.expr ctx.names t))
    | Subst (s, e) -> check_sort ctx (subst s e)
    | Lambda _ -> Error.typing ~loc "this expression is a function but should be a sort"
    | Pi (x, t1, t2) ->
      let u1 = check_sort ctx t1 in
      let u2 = check_sort (add_parameter x t1 ctx) t2 in
        max_size u1 u2
    | App (e1, e2) ->
      let (x, t1, t2) = infer_pi ctx e1 in
        check ctx e2 t1 ;
        check_sort (add_parameter x t1 ctx) t2
    | Ascribe (e1, e2) ->
      check ctx e1 e2 ;
      check_sort ctx e1
    | Type -> Large
    | Sort -> Error.typing ~loc "Sort is not a sort"

and infer_pi ctx e =
  let t = infer ctx e in
    match fst (Norm.whnf ctx t) with
      | Pi (x, t1, t2) -> (x, t1, t2)
      | Subst _ | Ascribe _ -> assert false
      | Var _ | App _ | Type | Sort | Lambda _ ->
        Error.typing ~loc:(snd e) "this expression has sort %t@ but it should be a function" (Print.expr ctx.names t)
