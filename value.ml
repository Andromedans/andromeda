type variable = Syntax.variable

type universe = int

type value =
  | Neutral of neutral
  | Universe of universe
  | Pi of abstraction
  | Lambda of abstraction

and neutral =
  | Var of variable
  | App of neutral * value

and abstraction = value * variable * (value -> value)

let rec eval env = function
  | Syntax.Var x ->
    (match Common.lookup x env with
      | Some v -> v
      | None -> Neutral (Var x))
  | Syntax.Universe u -> Universe u
  | Syntax.Pi a -> Pi (eval_abstraction env a)
  | Syntax.Lambda a -> Lambda (eval_abstraction env a)
  | Syntax.App (e1, e2) ->
    let v2 = eval env e2 in
      (match eval env e1 with
        | Lambda (_, _, f) -> f v2
        | Neutral n -> Neutral (App (n, v2))
        | _ -> Error.runtime "function expected")

and eval_abstraction env (x, t, e) =
  (eval env t, x, fun v -> eval (Common.extend x v env) e)

let rec equal_value v1 v2 =
  match v1, v2 with
    | Neutral n1, Neutral n2 -> equal_neutral n1 n2
    | Universe u1, Universe u2 -> u1 = u2
    | Pi a1, Pi a2 -> equal_abstraction a1 a2
    | Lambda a1, Lambda a2 -> equal_abstraction a1 a2
    | (Neutral _ | Universe _ | Pi _ | Lambda _), _ -> false

and equal_abstraction (v1, x, f1) (v2, _, f2) =
  v1 = v2 && (let x = Neutral (Var (Syntax.fresh_var x)) in equal_value (f1 x) (f2 x))

and equal_neutral n1 n2 =
  match n1, n2 with
    | Var x, Var y -> x = y
    | App (m1, v1), App (m2, v2) -> equal_neutral m1 m2 && equal_value v1 v2
    | (Var _ | App _), _ -> false

let rec uneval = function
  | Neutral n -> uneval_neutral n
  | Universe u -> Syntax.Universe u
  | Pi a -> Syntax.Pi (uneval_vabstraction a)
  | Lambda a -> Syntax.Lambda (uneval_vabstraction a)

and uneval_neutral = function
  | Var x -> Syntax.Var x
  | App (n, v) -> Syntax.App (uneval_neutral n, uneval v)      

and uneval_vabstraction (t, x, f) =
  let x = Syntax.fresh_var x in
    (x, uneval t, uneval (f (Neutral (Var x))))

