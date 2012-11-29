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

and abstraction = string * value * value

let mk_var k = Neutral (Var k)
let mk_app n v = Neutral (App (n, v))

let var0 = mk_var 0

let rec shift k = function
  | Neutral n -> Neutral (shift_neutral k n)
  | Universe _ as v -> v
  | Pi a -> Pi (shift_abstraction k a)
  | Lambda a -> Lambda shift_abstraction k a)

and shift_abstraction k (x, v1, v2) =
 (x, shift k v1, shift 


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
