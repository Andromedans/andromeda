(** Patterns are common to desugared syntax and runtime syntax. *)

type 'a located = 'a Location.located

(** Bound variables are de Bruijn indices *)
type bound = int


(** Term pattern *)
type is_term = is_term' located
and is_term' =
  | Term_Anonymous
  | Term_As of is_term * bound
  | Term_Bound of bound
  | Term_Type
  | Term_Constant of Name.ident
  | Term_Lambda of Name.ident * bound option * is_type option * is_term
  | Term_Apply of is_term * is_term
  | Term_Refl of is_term
  | Term_GenAtom of is_term
  | Term_GenConstant of is_term

(** Type pattern *)
and is_type = is_type' located
and is_type' =
  | Type_Prod of Name.ident * bound option * is_type option * is_type
  | Type_Eq of is_type * is_type

(** Term equality pattern *)
type eq_term = eq_term' located
and eq_term' = EqTerm of is_term * is_term * is_type

(** Type equality pattern *)
type eq_type = eq_type' located
and eq_type' = EqType of is_type * is_type

(** AML pattern *)
type pattern = pattern' located
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * bound
  | Patt_Bound of bound
  | Patt_Is_term of is_term * is_type
  | Patt_Is_type of is_type
  | Patt_Eq_term of is_term * is_term * is_type
  | Patt_Eq_type of is_type * is_type
  | Patt_Constructor of Name.ident * pattern list
  | Patt_Tuple of pattern list
