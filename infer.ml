(** Type inference and normalization. *)

open Syntax

(** [normalize ctx e] normalizes the given expression [e] in context [ctx]. It removes
    all redexes and it unfolds all definitions. It performs normalization under binders.  *)
let rec normalize ctx = function
  | Var x ->
    (match
        (try Ctx.lookup_value x ctx
         with Not_found -> Error.runtime "unkown identifier %t" (Print.variable x))
     with
       | None -> Var x
       | Some e -> normalize ctx e)
  | App (e1, e2) ->
    let e2 = normalize ctx e2 in
      (match normalize ctx e1 with
        | Lambda (x, _, e1') -> normalize ctx (subst [(x,e2)] e1')
        | e1 -> App (e1, e2))
  | Universe k -> Universe k
  | Pi a -> Pi (normalize_abstraction ctx a)
  | Lambda a -> Lambda (normalize_abstraction ctx a)

and normalize_abstraction ctx (x, t, e) =
  let t = normalize ctx t in
    (x, t, normalize (Ctx.extend x t ctx) e)

(** [equal ctx e1 e2] determines whether normalized [e1] and [e2] are equal up to renaming
    of bound variables. *)
let equal ctx e1 e2 =
  let rec equal e1 e2 =
    match e1, e2 with
      | Var x1, Var x2 -> x1 = x2
      | App (e11, e12), App (e21, e22) -> equal e11 e21 && equal e12 e22
      | Universe u1, Universe u2 -> u1 = u2
      | Pi a1, Pi a2 -> equal_abstraction a1 a2
      | Lambda a1, Lambda a2 -> equal_abstraction a1 a2
      | (Var _ | App _ | Universe _ | Pi _ | Lambda _), _ -> false
  and equal_abstraction (x, t1, e1) (y, t2, e2) =
    equal t1 t2 && (equal e1 (subst [(y, Var x)] e2))
  in
    equal (normalize ctx e1) (normalize ctx e2)

(** [infer_type ctx e] infers the type of expression [e] in context [ctx].  *)
let rec infer_type ctx = function
  | Var x ->
    (try Ctx.lookup_ty x ctx
     with Not_found -> Error.typing "unkown identifier %t" (Print.variable x))
  | Universe u -> Universe (u + 1)
  | Pi (x, t1, t2) ->
    let u1 = infer_universe ctx t1 in
    let u2 = infer_universe (Ctx.extend x t1 ctx) t2 in
      Universe (max u1 u2)
  | Lambda (x, t, e) ->
    let _ = infer_universe ctx t in
    let te = infer_type (Ctx.extend x t ctx) e in
      Pi (x, t, te)
  | App (e1, e2) ->
    let (x, s, t) = infer_pi ctx e1 in
    let te = infer_type ctx e2 in
      check_equal ctx s te ;
      subst [(x, e2)] t

(** [infer_universe ctx t] infers the universe level of type [t] in context [ctx]. *)
and infer_universe ctx t =
  let u = infer_type ctx t in
    match normalize ctx u with
      | Universe u -> u
      | App _ | Var _ | Pi _ | Lambda _ -> Error.typing "type expected"

(** [infer_pi ctx e] infers the type of [e] in context [ctx], verifies that it is
    of the form [Pi (x, t1, t2)] and returns the triple [(x, t1, t2)]. *)
and infer_pi ctx e =
  let t = infer_type ctx e in
    match normalize ctx t with
      | Pi a -> a
      | Var _ | App _ | Universe _ | Lambda _ -> Error.typing "function expected"

(** [check_equal ctx e1 e2] checks that expressions [e1] and [e2] are equal. *)
and check_equal ctx e1 e2 =
  if not (equal ctx e1 e2)
  then Error.typing "expressions %t and %t are not equal" (Print.expr e1) (Print.expr e2)
