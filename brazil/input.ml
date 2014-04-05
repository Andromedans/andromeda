type name = string

(** Users refer to variables as strings *)
type variable = string

(** At the input level we only have expressions, which can refer either to terms
    or types. This is so because we do not distinguish between types and their names.
    A desugaring phase figures out what is what. *)

type ty = expr

and expr = expr' * Position.t

and expr' =
  (* terms *)
  | Var of variable
  | Hint of term * term
  | Ascribe of term * ty
  | Lambda of name * ty * term
  | App of term * term
  | UnitTerm
  | Idpath of term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of term
  | G of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Coerce of Universe.t * * term
  (* types or their names *)
  | Universe of Universe.t
  | Unit
  | Prod of name * ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

