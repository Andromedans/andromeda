let anonymous = "_"

(** Users refer to variables as strings *)
type variable = string

(** At the input level we only have expressions, which can refer either to terms
    or types. This is so because we do not distinguish between types and their names.
    A desugaring phase figures out what is what. *)

type universe = Universe.t * Position.t

type ty = expr

and term = expr

and expr = expr' * Position.t

and expr' =
  (* terms *)
  | Var of variable (* x *)
  | Equation of term * term (* equation e1 in e2 *)
  | Rewrite of term * term (* rewrite e1 in e2 *)
  | Ascribe of term * ty (* e :: T *)
  | Lambda of variable * ty * ty * term (* fun (x : T) [U] => e *)
  | App of (variable * ty * ty) * term * term (* e1 @[x : T . U] e2 *)
  | UnitTerm (* () *)
  | Idpath of ty * term (* idpath [T] e *)
  | J of ty * (variable * variable * variable * ty) * (variable * term) * term * term * term
    (* J (T, [x . y . p . U], [z . e1], e2, e3, e4) *)
  | Refl of ty * term (* refl T e *)
  | Coerce of universe * universe * term (* coerce i j e *)
  (* types or their variables *)
  | Universe of universe (* Universe i *)
  | Unit (* unit *)
  | Prod of variable * ty * ty (* forall (x : T) , U *)
  | Paths of ty * term * term (* e1 = e2 @ T *)
  | Id of ty * term * term (* e1 == e2 @ T *)

type toplevel = toplevel' * Position.t
and toplevel' =
  | Help (* #help *)
  | Quit (* #quit *)
  | Context (* #context *)
  | Assume of variable list * ty (* assume x1 ... xn : t *)
  | Define of variable * ty * term (* define x : T := e *)
