type ty =
  | Ty of Syntax.ty
  | El of Universe.t * term
  | Prod of ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

and term =
  | Term of Syntax.term
  | PVar of int
  | Lambda of ty * ty * term
  | App of (ty * ty) * term * term
  | Idpath of ty * term
  | J of ty * (ty) * (term) * term * term * term
  | Refl of ty * term
  | Coerce of Universe.t * Universe.t * term
  | NameProd of Universe.t * Universe.t * term * term
  | NamePaths of Universe.t * term * term * term
  | NameId of Universe.t * term * term * term

val of_ty : int -> Syntax.ty -> ty

val of_term : int -> Syntax.term -> term

val shift_ty : int -> ty -> ty

val shift : int -> term -> term
