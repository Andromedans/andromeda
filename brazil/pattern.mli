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

val subst_term : (int * Syntax.term) list -> int -> term -> term

val subst_ty : (int * Syntax.term) list -> int -> ty -> ty

(* Spines *)

exception NoSpine

type ('y,'r) spine = head * ((name * 'y * 'y) * 'r) list

and head =
  | HVar of int   (* Brazil variable, not a pattern variable! *)
  | HNameProd of Universe.t * Universe.t
  | HNamePaths of Universe.t
  | HNameId of Universe.t
  | HNameUniverse of Universe.t
  | HCoerce of Universe.t * Universe.t
  | HRefl of Syntax.ty
  | HIdpath of Syntax.ty
  | HUnitTerm
  | HNameUnit

val eq_head : (Syntax.ty -> Syntax.ty -> bool) -> head -> head -> bool

val spine_of_term : term -> (ty, term) spine
val spine_of_brazil : Syntax.term -> (Syntax.ty, Syntax.term) spine

val subst_pattern_args :
    (int * Syntax.term) list ->
    int ->
    ((name * ty * ty) * term) list ->
    ((name * ty * ty) * term) list




