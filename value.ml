(** Values used for normalization-by-evaluation. *)

(** The type of values. The [Neutral] values are applications whose head is a variable. *)
type value =
  | Neutral of neutral
  | Universe of int
  | Pi of abstraction
  | Lambda of abstraction

and neutral =
  | Var of int
  | App of neutral * value

and abstraction = string * value * (value -> value)

let var0 = Neutral (Var 0)

(** Comparison of values for equality. It descends into abstractions by first applying them
    to freshly generated variables, which has the effect of alpha-equivalence. *)
let rec equal v1 v2 =
  match v1, v2 with
    | Neutral n1, Neutral n2 -> equal_neutral n1 n2
    | Universe k1, Universe k2 -> k1 = k2
    | Pi a1, Pi a2 -> equal_abstraction a1 a2
    | Lambda a1, Lambda a2 -> equal_abstraction a1 a2
    | (Neutral _ | Universe _ | Pi _ | Lambda _), _ -> false

and equal_abstraction (_, v1, f1) (_, v2, f2) =
  equal v1 v2 && equal (f1 var0) (f2 var0)

and equal_neutral n1 n2 =
  match n1, n2 with
    | Var x1, Var x2 -> x1 = x2
    | App (n1, v1), App (n2, v2) -> equal_neutral n1 n2 && equal v1 v2
    | (Var _ | App _), _ -> false

(** [eval env e] evaluates expression [e] in environment [env] to a value. *)
let rec eval ctx ((e', loc) as e) =
  match e' with
    | Syntax.Var k ->
      (match Context.lookup_definition k ctx with
        | None -> Neutral (Var k)
        | Some e -> eval ctx e)
    | Syntax.Universe u -> Universe u
    | Syntax.Pi a -> Pi (eval_abstraction ctx a)
    | Syntax.Lambda a -> Lambda (eval_abstraction ctx a)
    | Syntax.Subst _ -> eval ctx (Syntax.reduce Syntax.idsubst e)
    | Syntax.App (e1, e2) ->
      let v2 = eval ctx e2 in
        (match eval ctx e1 with
          | Lambda (_, _, f) -> f v2
          | Neutral n -> Neutral (App (n, v2))
          | Universe _ | Pi _ -> Error.runtime ~loc:(snd e2) "Function expected")

and eval_abstraction ctx (x, t, e) =
  (x, eval ctx t, fun v -> eval (Context.extend x t ctx) e)

(** [eval' ctx e] is like [eval ctx e] except that [e] is an expression without
    position. *)
let eval' ctx e = eval ctx (Common.nowhere e)

(** [reify v] reifies value [v] to an expression. *)
let rec reify v = Common.nowhere (reify' v)

and reify' = function
  | Neutral n -> reify_neutral' n
  | Universe k -> Syntax.Universe k
  | Pi a -> Syntax.Pi (reify_abstraction a)
  | Lambda a -> Syntax.Lambda (reify_abstraction a)

and reify_abstraction (x, t, f) =
    (x, reify t, reify (f var0))

and reify_neutral n = Common.nowhere (reify_neutral' n)

and reify_neutral' = function
  | Var x -> Syntax.Var x
  | App (n, v) -> Syntax.App (reify_neutral n, reify v)
