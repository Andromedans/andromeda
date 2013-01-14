(** Type inference. *)

open Syntax
open Context

let rec equal_at ctx e1 e2 t =
  match fst (Norm.whnf ctx t) with
    | Pi (x, t1, t2) ->
      equal_at (add_parameter x t1 ctx) (mk_app e1 (mk_var 0)) (mk_app e2 (mk_var 0)) t2
    | Universe _ -> equal ctx e1 e2
    | App _ -> equal ctx e1 e2
    | Lambda _ | Var _ | Subst _ | Ascribe _ -> assert false

(** [equal ctx e1 e2] determines whether [e1] and [e2] are equal expressions. *)
and equal ctx e1 e2 =
  let (e1, _) = Norm.whnf ctx e1 in
  let (e2, _) = Norm.whnf ctx e2 in
    match e1, e2 with
      | Var k1, Var k2 -> k1 = k2
        if k1 = k2 then Some (lookup_ty k1 ctx) else None
      | Universe u1, Universe u2 ->
        if u1 = u2 then Some (mk_universe (u1 + 1)) else None
      | Pi (x, t1, t2), Pi (_, u1, u2) -> equal_abstraction ctx a1 a2
      | Lambda (_, e1), Lambda (_, e2) ->
        equal_abstraction ctx a1 a2
      | App (n1, e1), App (n2, e2) -> equal ctx n1 n2 && equal ctx e1 e2
      | (Var _ | Universe _ | Pi _ | Lambda _ | App _ | Subst _), _ -> None
        
and equal_abstraction ctx (x, t1, e2) (_, t1', e2') =
  match equal ctx t1 t1' with
    | None -> None
    | Some (Universe _) -> assert false
          
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
    | Lambda (x, e1, e2) ->
      let _ = infer_universe ctx e1 in
      let t2 = infer (add_parameter x e1 ctx) e2 in
        mk_pi (x, e1, t2)
    | App (e1, e2) ->
      let (x, s, t) = infer_pi ctx e1 in
      let t2 = infer ctx e2 in
        if not (equal ctx s t2)
        then
          Error.typing ~loc:(snd e2)
            "this expresion has type@ %t@ but@ %t@ was expected"
            (Print.expr ctx.names t2) (Print.expr ctx.names s)
        else
          mk_subst (Dot (e2, idsubst)) t

and check ctx ((e', loc) as e) t =
  let ok =
    match e' with
      | Var _ | Pi _ | App _ -> let t' = infer ctx e in equal ctx t t'
      | Universe u -> let v = infer_universe ctx t in u + 1 = v
      | Subst (s, e) -> check ctx (Syntax.subst s e)
      | Lambda (x, e) ->
        (match Norm.whnf ctx t with
          | Pi (_, t1, t2) -> check (add_parameter x t1 ctx) e t2
          | _ -> false)
      | Ascribe (e, t') -> check ctx e t' ; equal ctx t' t
  in
    Error.typing ~loc "this expression should have type@ %t@ but it does not" (Print.expr ctx.names t)

(** [infer_universe ctx t] infers the universe level of type [t] in context [ctx]. *)
and infer_universe ctx t =
  let u = infer ctx t in
    match fst (Norm.whnf ctx u) with
      | Universe u -> u
      | Subst _ | App _ | Var _ | Pi _ | Lambda _ ->
        Error.typing ~loc:(snd t) "this expression has type@ %t@ but it should be a universe" (Print.expr ctx.names u)

and infer_pi ctx e =
  let t = infer ctx e in
    match fst (Norm.whnf ctx t) with
      | Pi a -> a
      | Subst _ | Var _ | App _ | Universe _ | Lambda _ ->
        Error.typing ~loc:(snd e) "this expression has type@ %t@ but it should be a function" (Print.expr ctx.names t)
