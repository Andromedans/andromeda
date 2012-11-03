(** TT with pies and universes indexed by numerals *)

open Syntax
open Value

let disable_typing = ref false

let lookup x lst =
  try
    Some (List.assoc x lst)
  with Not_found -> None

let lookup_var x ctx =
  try
    List.assoc x ctx
  with Not_found -> Error.typing "unkown identifier %t" (Print.variable x)

let extend x y lst = (x,y) :: lst

let rec eval env = function
  | Var x ->
    (match lookup x env with
      | Some v -> v
      | None -> VNeutral (VVar x))
  | Universe u -> VUniverse u
  | Pi a -> VPi (eval_abstraction env a)
  | Lambda a -> VLambda (eval_abstraction env a)
  | App (e1, e2) ->
    let v2 = eval env e2 in
      (match eval env e1 with
        | VLambda (_, f) -> f v2
        | VNeutral n -> VNeutral (VApp (n, v2))
        | _ -> Error.runtime "function expected")

and eval_abstraction env (x, t, e) =
  (eval env t, fun v -> eval (extend x v env) e)

let rec uneval = function
  | VNeutral n -> uneval_neutral n
  | VUniverse u -> Universe u
  | VPi a -> Pi (uneval_vabstraction a)
  | VLambda a -> Lambda (uneval_vabstraction a)

and uneval_neutral = function
  | VVar x -> Var x
  | VApp (n, v) -> App (uneval_neutral n, uneval v)

and uneval_vabstraction (t, f) =
  let x = fresh_var (String "x") in
    (x, uneval t, uneval (f (VNeutral (VVar x))))

let rec equal_value v1 v2 =
  match v1, v2 with
    | VNeutral n1, VNeutral n2 -> equal_neutral n1 n2
    | VUniverse u1, VUniverse u2 -> u1 = u2
    | VPi a1, VPi a2 -> equal_vabstraction a1 a2
    | VLambda a1, VLambda a2 -> equal_vabstraction a1 a2
    | (VNeutral _ | VUniverse _ | VPi _ | VLambda _), _ -> false

and equal_vabstraction (v1, f1) (v2, f2) =
  v1 = v2 && (let x = VNeutral (VVar (fresh_var (String "y"))) in equal_value (f1 x) (f2 x))

and equal_neutral n1 n2 =
  match n1, n2 with
    | VVar x, VVar y -> x = y
    | VApp (m1, v1), VApp (m2, v2) -> equal_neutral m1 m2 && equal_value v1 v2
    | (VVar _ | VApp _), _ -> false

let rec fv lst = function
  | Var x -> if List.mem x lst then [] else [x]
  | Universe _ -> []
  | Pi (x, t1, t2) -> fv lst t1 @ (fv (x::lst) t2)
  | Lambda (x, t, e) -> fv lst t @ (fv (x::lst) e)
  | App (e1, e2) -> fv lst e1 @ fv lst e2

let refresh y sbst =
  let lst = List.fold_left (fun lst (_, e) -> fv [] e @ lst) [] sbst in
    if List.mem y lst
    then fresh_var y
    else y

let rec subst sbst = function
  | Var y ->
    (match lookup y sbst with
      | Some e -> e
      | None -> Var y)
  | Universe _ as e' -> e'
  | Pi (y, t1, t2) ->
    let z = refresh y sbst in
      Pi (z, subst sbst t1, subst (extend y (Var z) sbst) t2)
  | Lambda (y, t, e) ->
    let z = refresh y sbst in
      Lambda (z, subst sbst t, subst (extend y (Var z) sbst) e) 
  | App (e1, e2) -> App (subst sbst e1, subst sbst e2)

let rec infer_type ctx = function
  | Var x -> lookup_var x ctx
  | Universe u -> Universe (u + 1)
  | Pi (x, t1, t2) ->
    let u1 = infer_universe ctx t1 in
    let u2 = infer_universe (extend x t1 ctx) t2 in
      Universe (max u1 u2)
  | Lambda (x, t, e) ->
    check_type ctx t ;
    let s = infer_type (extend x t ctx) e in
      Pi (x, t, s)
  | App (e1, e2) ->
    let (t, f) = infer_pi ctx e1 in
    let r = infer_type ctx e2 in
      check_equal t r ;
      f e2

and infer_universe ctx t =
  let u = infer_type ctx t in
    match eval [] u with
      | VUniverse u -> u
      | VNeutral _ | VPi _ | VLambda _ -> Error.typing "type expected"

and check_type ctx t = ignore (infer_universe ctx t)

and infer_pi ctx e =
  let t = infer_type ctx e in
    match eval [] t with
      | VPi (t, f) -> (uneval t, fun e -> uneval (f (eval [] e)))
      | VUniverse _ | VNeutral _ | VLambda _ -> Error.typing "function expected"

and check_equal t1 t2 =
  if not (equal_value (eval [] t1) (eval [] t2)) then Error.typing "type mismatch"
