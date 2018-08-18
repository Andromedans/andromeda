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
  | Term_Constant of Name.ident
  | Term_Abstract of Name.ident * bound option * is_type option * is_term
  | Term_Apply of is_term * is_term
  | Term_GenAtom of is_term
  | Term_GenConstant of is_term

(** Type pattern *)
and is_type = is_type' located
and is_type' =
  | Type_Anonymous
  | Type_As of is_type * bound
  | Type_Bound of bound
  | Type_Type
  | Type_Prod of Name.ident * bound option * is_type option * is_type
  | Type_El of is_term

(** AML pattern *)
type aml = aml' located
and aml' =
  | Anonymous
  | As of aml * bound
  | Bound of bound
  | IsTerm of is_term * is_type
  | IsType of is_type
  | EqTerm of is_term * is_term * is_type
  | EqType of is_type * is_type
  | Constructor of Name.ident * aml list
  | Tuple of aml list
