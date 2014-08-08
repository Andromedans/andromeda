type label = Syntax.label

type name = string

type ty =
  | Ty of Syntax.ty
  | El of Universe.t * term
  | RecordTy of (label * (name * ty)) list
  | Prod of name * ty * ty
  | Paths of ty * term * term
  | Id of ty * term * term

and term =
  | Term of Syntax.term
  | PVar of int
  | Lambda of name * ty * ty * term
  | App of (name * ty * ty) * term * term
  | Spine of Syntax.variable * term list
  | Record of (label * (name * ty * term)) list
  | Project of term * (label * (name * ty * term)) list * label
  | Idpath of ty * term
  | J of ty * (name * name * name * ty) * (name * term) * term * term * term
  | Refl of ty * term
  | Coerce of Universe.t * Universe.t * term
  | NameRecordTy of (label * (name * Universe.t * term)) list
  | NameProd of Universe.t * Universe.t * name * term * term
  | NamePaths of Universe.t * term * term * term
  | NameId of Universe.t * term * term * term

val of_ty : int -> Syntax.ty -> ty

val of_term : int -> Syntax.term -> term

val shift_ty : int -> int -> ty -> ty

val shift : int -> int -> term -> term

val subst_term : (int * Syntax.term) list -> int -> term -> term

val subst_ty : (int * Syntax.term) list -> int -> ty -> ty

