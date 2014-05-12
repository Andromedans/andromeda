type name = string

type ty =
  | Ty of Syntax.ty
  | El of Universe.t * term
  | Prod of name * ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

and term =
  | Term of Syntax.term
  | PVar of int
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | Idpath of ty * term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of ty * term
  | Coerce of Universe.t * Universe.t * term
  | NameProd of Universe.t * Universe.t * name * term * term
  | NamePaths of Universe.t * term * term * term
  | NameId of Universe.t * term * term * term

val of_ty : int -> Syntax.ty -> ty

val of_term : int -> Syntax.term -> term

val shift_ty : int -> int -> ty -> ty

val shift : int -> int -> term -> term

val subst_term : (int * Syntax.term) list -> int -> term -> Syntax.term
