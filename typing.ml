(** Type checking and inference. *)

open Syntax
open Context

(** [eval env e] evaluates expression [e] in environment [env] to a value. *)
let rec eval ctx ((e', loc) as e) =
  match e' with
    | Var k ->
      (match Context.lookup_value k ctx with
        | None -> e
        | Some v -> v)
    | Universe _ -> e
    | Pi a -> Pi (eval_abstraction ctx a), loc
    | Lambda a -> Lambda (eval_abstraction ctx a), loc
    | Subst _ -> eval ctx (reduce idsubst e)
    | App (e1, e2) ->
      let v2 = eval ctx e2 in
        (match eval ctx e1 with
          | Lambda (_, _, v1) -> eval (Context.add_value v2 ctx) v1
          | App _ as v1 -> App (v1, v2), loc
          | Universe _ | Pi _ -> Error.runtime ~loc:(snd e2) "Function expected")

and eval_abstraction ctx (x, t, e) =
  (x, eval ctx t, eval (Context.add_parameter x t ctx) e)

(** [reify v] reifies value [v] to an expression. *)
let rec reify v = Common.nowhere (reify' v)

and reify = function
  | Value.Neutral n -> reify_neutral n
  | Value.Universe u -> mk_universe u
  | Value.Pi a -> mk_pi (reify_abstraction a)
  | Value.Lambda a -> mk_lambda (reify_abstraction a)

and reify_abstraction (x, v1, v2) =
    (x, reify v1, reify v2)

and reify_neutral = function
  | Value.Var k -> mk_var x
  | Value.App (n, v) -> mk_app (reify_neutral n) (reify v)

(** [normalize ctx e] normalizes the given expression [e] in context [ctx]. It removes
    all redexes and it unfolds all definitions. It performs normalization under binders.
    We use the "normalization by evaluation" technique, in which the expression is
    evaluated to an Ocaml value, which is then reified back to an expression. The effect
    of this is that two equal expressions get evaluated to (observationally) equivalent
    values, and hence their reification are syntactically equal (up to renaming of bound
    variables.) *)
let normalize ctx e = reify (eval ctx e)

(** [equal ctx e1 e2] compares expressions [e1] and [e2] for equality. *)
let equal ctx e1 e2 = Value.equal (Value.eval ctx e1) (Value.eval ctx e2)

let index ~loc x ctx =
  let rec index k = function
    | [] -> Error.typing ~loc "unknown identifier %s" x
    | y :: ys -> if x = y then k else index (k + 1) ys
  in
    index 0 ctx.names

(** [infer ctx e] infers the type of expression [e] of type [Input.expr] in context [ctx].
    It returns the expression converted to type [expr], its type, and a solution for
    the existential variables. *)
let rec infer ctx (e, loc) : expr * expr =
  match e with
    | Input.Var x -> 
      let k = index ~loc x ctx in
        (Var k, loc), lookup_ty k ctx
    | Input.Universe u -> (Universe u, loc), mk_universe (u + 1)
    | Input.Pi (x, e1, e2) ->
      let e1, u1 = infer_universe ctx e1 in
      let e2, u2 = infer_universe (extend x e1 ctx) e2 in
        (Pi (x, e1, e2), loc),
        mk_universe (max u1 u2)
    | Input.Lambda (x, e1, e2) ->
      let e1, _ = infer_universe ctx e1 in
      let e2, t2 = infer (extend x e1 ctx) e2 in
        (Lambda (x, e1, e2), loc),
        mk_pi (x, e1, t2)
    | Input.App (e1, e2) ->
      let e1, (x, s, t) = infer_pi ctx e1 in
      let e2, t2 = infer ctx e2 in
        if not (equal ctx s t2)
        then
          Error.typing ~loc:(snd e2)
            "this expresion has type@ %t@ but@ %t@ was expected"
            (Print.expr ctx.names t2) (Print.expr ctx.names s)
        else
          (App (e1, e2), loc), 
          mk_subst (Dot (e2, idsubst)) t

(** [infer_universe ctx t] infers the universe level of type [t] in context [ctx]. *)
and infer_universe ctx t =
  let t, u = infer ctx t in
    match fst (normalize ctx u) with
      | Universe u -> t, u
      | Subst _ | App _ | Var _ | Pi _ | Lambda _ ->
        Error.typing ~loc:(snd t) "this expression has type@ %t@ but it should be a universe" (Print.expr ctx.names u)

and infer_pi ctx e =
  let e, t = infer ctx e in
    match fst (normalize ctx t) with
      | Pi a -> e, a
      | Subst _ | Var _ | App _ | Universe _ | Lambda _ ->
        Error.typing ~loc:(snd e) "this expression has type@ %t@ but it should be a function" (Print.expr ctx.names t)
