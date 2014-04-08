(** Abstract syntax for Brazilian type theory. *)

type name = string

(** We use de Bruijn indices *)
type variable = int

type ty = ty' * Position.t
and ty' =
  | Universe of Universe.t
  | El of term
  | Unit
  | Prod of name * ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

and term = term' * Position.t
and term' =
  | Var of variable
  | Equation of term * term
  | Rewrite of term * term
  | Ascribe of term * ty
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | UnitTerm
  | Idpath of ty * term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of ty * term
  | Coerce of Universe.t * Universe.t * term
  | NameProd of name * term * term
  | NameUniverse of Universe.t
  | NamePaths of term * term * term
  | NameId of term * term * term
