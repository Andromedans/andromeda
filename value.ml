type variable = Syntax.variable

type value =
  | Neutral of neutral
  | Universe of int
  | Pi of abstraction
  | Lambda of abstraction

and abstraction = variable * value * (value -> value)

and neutral =
  | Var of variable
  | App of neutral * value

let rec equal v1 v2 =
  match v1, v2 with
    | Neutral n1, Neutral n2 -> equal_neutral n1 n2
    | Universe k1, Universe k2 -> k1 = k2
    | Pi a1, Pi a2 -> equal_abstraction a1 a2
    | Lambda a1, Lambda a2 -> equal_abstraction a1 a2
    | (Neutral _ | Universe _ | Pi _ | Lambda _), _ -> false

and equal_abstraction (x, v1, f1) (_, v2, f2) =
  equal v1 v2 &&
    (let x = Neutral (Var (Syntax.refresh x)) in equal (f1 x) (f2 x))

and equal_neutral n1 n2 =
  match n1, n2 with
    | Var x1, Var x2 -> x1 = x2
    | App (n1, v1), App (n2, v2) -> equal_neutral n1 n2 && equal v1 v2
    | (Var _ | App _), _ -> false

let eval ctx =
  let rec eval env (e, loc) =
    match e with
      | Syntax.Var x ->
        begin
          try List.assoc x env
          with Not_found ->
            begin
              match
                (try Ctx.lookup_value x ctx
                 with Not_found -> Error.runtime "unkown identifier %t" (Print.variable x))
              with
                | None -> Neutral (Var x)
                | Some e -> eval env e
            end
        end
      | Syntax.Universe k -> Universe (k+1)
      | Syntax.Pi a -> Pi (eval_abstraction env a)
      | Syntax.Lambda a -> Lambda (eval_abstraction env a)
      | Syntax.App (e1, e2) ->
        let v2 = eval env e2 in
        (match eval env e1 with
          | Lambda (_, _, f) -> f v2
          | Neutral n -> Neutral (App (n, v2))
          | Universe _ | Pi _ -> Error.runtime "Function expected")
  and eval_abstraction env (x, t, e) =
    (x, eval env t, fun v -> eval ((x, v) :: env) e)
  in
    eval []

let rec reify x = Syntax.nowhere (reify' x)

and reify' = function
  | Neutral n -> reify_neutral' n
  | Universe k -> Syntax.Universe k
  | Pi a -> Syntax.Pi (reify_abstraction a)
  | Lambda a -> Syntax.Lambda (reify_abstraction a)

and reify_abstraction (x, t, f) =
  let x = Syntax.refresh x in
    (x, reify t, reify (f (Neutral (Var x))))

and reify_neutral n = Syntax.nowhere (reify_neutral' n)

and reify_neutral' = function
  | Var x -> Syntax.Var x
  | App (n, v) -> Syntax.App (reify_neutral n, reify v)
