(** Type checking and inference. *)

open Syntax
open Context

(** [norm env e] evaluates expression [e] in environment [env] to a value. *)
let norm ?(weak=false) =
  let rec norm ctx ((e', loc) as e) =
    match e' with
      | Var k ->
        (match Context.lookup_definition k ctx with
          | None -> e
          | Some e -> norm ctx e)
      | Universe _ -> e
      | Pi a -> 
        Pi (norm_abstraction ctx a), loc
      | Lambda a -> Lambda (norm_abstraction ctx a), loc
      | Subst _ -> norm ctx (reduce idsubst e)
      | App (e1, e2) ->
        let (e1', _) as e1 = norm ctx e1 in
          (match e1' with
            | Lambda (x, _, e) ->
                norm ctx (mk_subst (Dot (e2, idsubst)) e)
            | Var _ | App _ -> 
              let e2 = (if weak then e2 else norm ctx e2) in 
                App (e1, e2), loc
            | Subst _ | Universe _ | Pi _ -> Error.runtime ~loc:(snd e2) "Function expected")
  and norm_abstraction ctx ((x, t, e) as a) =
    if weak
    then a
    else (x, norm ctx t, norm (Context.add_parameter x t ctx) e)
  in
    norm

let nf = norm ~weak:false

let hnf = norm ~weak:true

let rec equal ctx e1 e2 =
  let (e1, _) = hnf ctx e1 in
  let (e2, _) = hnf ctx e2 in
    match e1, e2 with
      | Var k1, Var k2 -> k1 = k2
      | Universe u1, Universe u2 -> u1 = u2
      | Pi a1, Pi a2 -> equal_abstraction ctx a1 a2
      | Lambda a1, Lambda a2 -> equal_abstraction ctx a1 a2
      | App (n1, e1), App (n2, e2) -> equal ctx n1 n2 && equal ctx e1 e2
      | (Var _ | Universe _ | Pi _ | Lambda _ | App _ | Subst _), _ -> false

and equal_abstraction ctx (x, e1, e2) (_, e1', e2') =
  equal ctx e1 e1' && equal (Context.add_parameter x e1 ctx) e2 e2'

let index ~loc x ctx =
  let rec index k = function
    | [] -> Error.typing ~loc "unknown identifier %s" x
    | y :: ys -> if x = y then k else index (k + 1) ys
  in
    index 0 ctx.names

(** [infer ctx e] infers the type of expression [e] of type [Input.expr] in context [ctx].
    It returns the expression converted to type [expr] and its type. *)
let rec infer ctx (e, loc) : expr * expr =
  match e with
    | Input.Var x -> 
      let k = index ~loc x ctx in
        (Var k, loc), lookup_ty k ctx
    | Input.Universe u -> (Universe u, loc), mk_universe (u + 1)
    | Input.Pi (x, e1, e2) ->
      let e1, u1 = infer_universe ctx e1 in
      let e2, u2 = infer_universe (add_parameter x e1 ctx) e2 in
        (Pi (x, e1, e2), loc),
        mk_universe (max u1 u2)
    | Input.Lambda (x, e1, e2) ->
      let e1, _ = infer_universe ctx e1 in
      let e2, t2 = infer (add_parameter x e1 ctx) e2 in
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
    match fst (hnf ctx u) with
      | Universe u -> t, u
      | Subst _ | App _ | Var _ | Pi _ | Lambda _ ->
        Error.typing ~loc:(snd t) "this expression has type@ %t@ but it should be a universe" (Print.expr ctx.names u)

and infer_pi ctx e =
  let e, t = infer ctx e in
    match fst (hnf ctx t) with
      | Pi a -> e, a
      | Subst _ | Var _ | App _ | Universe _ | Lambda _ ->
        Error.typing ~loc:(snd e) "this expression has type@ %t@ but it should be a function" (Print.expr ctx.names t)
