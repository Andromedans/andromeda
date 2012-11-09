(** Type inference and normalization. *)

open Syntax
open Ctx

(** [normalize ctx e] normalizes the given expression [e] in context [ctx]. It removes
    all redexes and it unfolds all definitions. It performs normalization under binders.  *)
let normalize ctx e = Value.reify' (Value.eval ctx e)

(** [infer_type ctx e] infers the type of expression [e] in context [ctx].  *)
let rec infer_type ctx (e, loc) : expr' =
  match e with
    | Var x ->
      (try lookup_ty x ctx
       with Not_found -> Error.typing "unkown identifier %t" (Print.variable x))
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
        check_equal ctx s (te, snd e2) ;
        fst (subst [(x, fst e2)] t)

(** [infer_universe ctx t] infers the universe level of type [t] in context [ctx]. *)
and infer_universe ctx t =
  let u = infer_type ctx t in
    match normalize ctx (u, snd t) with
      | Universe k -> k
      | App _ | Var _ | Pi _ | Lambda _ -> Error.typing "type expected"

(** [infer_pi ctx e] infers the type of [e] in context [ctx], verifies that it is
    of the form [Pi (x, t1, t2)] and returns the triple [(x, t1, t2)]. *)
and infer_pi ctx e =
  let t = infer_type ctx e in
    match normalize ctx (t, snd e) with
      | Pi a -> a
      | Var _ | App _ | Universe _ | Lambda _ -> Error.typing "function expected"

(** [check_equal ctx e1 e2] checks that expressions [e1] and [e2] are equal. *)
and check_equal ctx e1 e2 =
  let v1 = Value.eval ctx e1 in
  let v2 = Value.eval ctx e2 in
    if not (Value.equal v1 v2)
  then Error.typing "expressions %t and %t are not equal" (Print.expr e1) (Print.expr e2)
