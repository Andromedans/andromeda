open Syntax

(* Contexts *)
let lookup x ctx = List.assoc x ctx

let lookup_ty x ctx = fst (lookup x ctx)

let lookup_value x ctx = snd (lookup x ctx)

let extend x t ?value lst = (x, (t, value)) :: lst

(* Normalization. *)
let rec normalize ctx = function
  | Var x ->
    (match
        (try lookup_value x ctx
         with Not_found -> Error.runtime "unkown identifier %t" (Print.variable x))
     with
       | None -> Var x
       | Some e -> normalize ctx e)
  | App (e1, e2) ->
    let e2 = normalize ctx e2 in
      (match normalize ctx e1 with
        | Lambda (_, _, f) -> normalize ctx (f e2)
        | e1 -> App (e1, e2))
  | Universe k -> Universe k
  | Pi a -> Pi (normalize_abstraction ctx a)
  | Lambda a -> Lambda (normalize_abstraction ctx a)

and normalize_abstraction ctx (x, t, f) =
  let t = normalize ctx t in
  let x = Concrete.fresh_var x in
  let f v = normalize (extend x t ~value:v ctx) (f (Var x)) in
    (x, t, f)

(* Equality of expressions. *)
let rec equal ctx e1 e2 =
  match normalize ctx e1, normalize ctx e2 with
    | Var x1, Var x2 -> x1 = x2
    | App (e11, e12), App (e21, e22) -> equal ctx e11 e21 && equal ctx e12 e22
    | Universe u1, Universe u2 -> u1 = u2
    | Pi a1, Pi a2 -> equal_abstraction ctx a1 a2
    | Lambda a1, Lambda a2 -> equal_abstraction ctx a1 a2
    | (Var _ | App _ | Universe _ | Pi _ | Lambda _), _ -> false

and equal_abstraction ctx (x, t1, f1) (_, t2, f2) =
  equal ctx t1 t2 &&
  (let x = Concrete.fresh_var x in
     equal (extend x t1 ctx) (f1 (Var x)) (f2 (Var x)))

(* Type inference. *)
let rec infer_type ctx = function
  | Var x ->
    (try lookup_ty x ctx
     with Not_found -> Error.typing "unkown identifier %t" (Print.variable x))
  | Universe u -> Universe (u + 1)
  | Pi (x, t1, t2) ->
    let u1 = infer_universe ctx t1 in
    let x = Concrete.fresh_var x in
    let ctx = extend x t1 ctx in
    let u2 = infer_universe ctx (t2 (Var x)) in
      Universe (max u1 u2)
  | Lambda (x, t, e) ->
    let _ = infer_universe ctx t in
    let x = Concrete.fresh_var x in
    let f v = infer_type (extend x t ~value:v ctx) (e (Var x)) in
      Pi (x, t, f)
  | App (e1, e2) ->
    let (t1, f1) = infer_pi ctx e1 in
    let t2 = infer_type ctx e2 in
      check_equal ctx t1 t2 ;
      f1 e2

and infer_universe ctx t =
  let u = infer_type ctx t in
    match normalize ctx u with
      | Universe u -> u
      | App _ | Var _ | Pi _ | Lambda _ -> Error.typing "type expected"

and infer_pi ctx e =
  let t = infer_type ctx e in
    match normalize ctx t with
      | Pi (_, t, f) -> (t, f)
      | Var _ | App _ | Universe _ | Lambda _ -> Error.typing "function expected"

and check_equal ctx t1 t2 =
  if not (equal ctx t1 t2)
  then Error.typing "expressions %t and %t are not equal" (Print.expr t1) (Print.expr t2)
