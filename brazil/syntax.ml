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
  | Hint of term * term
  | Ascribe of term * ty
  | Lambda of name * ty * term
  | App of term * term
  | UnitTerm
  | Idpath of term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of term
  | G of ty * (name * name * name * ty) * (name * term) * term * term * term
  | NameProd of Universe.t * Universe.t * name * term * term
  | NameUniverse of Universe.t
  | Coerce of Universe.t * Universe.t * term
  | NamePaths of Universe.t * term * term * term
  | NameId of Universe.t * term * term * term
