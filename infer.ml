(** Type inference and normalization. *)

open Syntax
open Ctx

(** [normalize ctx e] normalizes the given expression [e] in context [ctx]. It removes
    all redexes and it unfolds all definitions. It performs normalization under binders.
    We use the "normalization by evaluation" technique, in which the expression is
    evaluated to an Ocaml value, which is then reified back to an expression. The effect
    of this is that two equal expressions get evaluated to (observationally) equivalent
    values, and hence their reification are syntactically equal (up to renaming of bound
    variables. *)
let normalize ctx e = Value.reify (Value.eval ctx e)

let normalize' ctx e = Value.reify' (Value.eval' ctx e)


(** [equal ctx e1 e2] compares expressions [e1] and [e2] for equality. *)
let equal ctx e1 e2 = Value.equal (Value.eval' ctx e1) (Value.eval' ctx e2)

(** [infer_type ctx e] infers the type of expression [e] in context [ctx].  *)
let rec infer_type ctx (e, loc) : expr' =
  match e with
    | Var x ->
      (try lookup_ty x ctx
       with Not_found -> Error.typing ~loc "unkown identifier %t" (Print.variable x))
    | Universe k -> Universe (k + 1)
    | Pi (x, t1, t2) ->
      let k1 = infer_universe ctx t1 in
      let k2 = infer_universe (extend x (fst t1) ctx) t2 in
        Universe (max k1 k2)
    | Lambda (x, t, e) ->
      let _ = infer_universe ctx t in
      let te = infer_type (extend x (fst t) ctx) e in
        Pi (x, t, nowhere te)
    | App (e1, e2) ->
      let (x, s, t) = infer_pi ctx e1 in
      let te = infer_type ctx e2 in
        if not (equal ctx (fst s) te)
        then Error.typing ~loc:(snd e2) "this expresion has type@;@[%t@]@;but@;@[%t@]@;was expected" (Print.expr' te) (Print.expr s) ;
        fst (subst [(x, fst e2)] t)

(** [infer_universe ctx t] infers the universe level of type [t] in context [ctx]. *)
and infer_universe ctx t =
  let u = infer_type ctx t in
    match normalize' ctx u with
      | Universe k -> k
      | App _ | Var _ | Pi _ | Lambda _ ->
        Error.typing ~loc:(snd t) "this expression has type@;@[%t@]@;but it should be a universe" (Print.expr' u)

(** [infer_pi ctx e] infers the type of [e] in context [ctx], verifies that it is
    of the form [Pi (x, t1, t2)] and returns the triple [(x, t1, t2)]. *)
and infer_pi ctx e =
  let t = infer_type ctx e in
    match normalize' ctx t with
      | Pi a -> a
      | Var _ | App _ | Universe _ | Lambda _ ->
        Error.typing ~loc:(snd e) "this expression has type@;@[%t@]@;but it should be a function" (Print.expr' t)
