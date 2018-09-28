(** Patterns are common to desugared syntax and runtime syntax. *)

type 'a located = 'a Location.located

(** Bound variables are de Bruijn indices *)
type bound = int

(** Type pattern *)
type is_type = is_type' located
and is_type' =
  | IsType_Anonymous
  | IsType_NewVar of bound
  | IsType_EquVar of bound
  | IsType_Interpolate of bound
  | IsType_As of is_type * is_type
  | IsType_Constructor of Name.constructor * argument list

(** Term pattern *)
and is_term = is_term' located
and is_term' =
  | IsTerm_Anonymous
  | IsTerm_NewVar of bound
  | IsTerm_Equar of bound
  | IsTerm_Interpolate of bound
  | IsTerm_As of is_term * is_term
  | IsTerm_Constructor of Name.constructor * argument list
  | IsTerm_GenAtom of is_term

(** Term equality pattern *)
and eq_term = eq_term' located
and eq_term' =
  | EqTerm_Anonymous
  | EqTerm_NewVar of bound
  | EqTerm_EquVar of bound
  | EqTerm_Interpolate of bound
  | EqTerm_As of eq_term * eq_term
  | EqTerm_Eq of is_term * is_term * is_type

(** Type equality pattern *)
and eq_type = eq_type' located
and eq_type' =
  | EqType_Anonymous
  | EqType_NewVar of bound
  | EqType_EquVar of bound
  | EqType_Interpolate of bound
  | EqType_As of eq_type * eq_type
  | EqType_Eq of is_type * is_type

(** Patterns for constructor arguments *)
and argument =
  | ArgIsType of is_type abstraction
  | ArgIsTerm of is_term abstraction
  | ArgEqType of eq_type abstraction
  | ArgEqTerm of eq_term abstraction

(** An abstracted pattern *)
and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.ident * bound option * is_type option * 'a

(** AML pattern *)
type aml = aml' located
and aml' =
  | Anonymous
  | NewVar of bound
  | EquVar of bound
  | Interpolate of bound
  | As of aml * aml
  | IsTerm of is_term abstraction
  | IsType of is_type abstraction
  | EqTerm of (is_term * is_term * is_type) abstraction
  | EqType of (is_type * is_type) abstraction
  | Constructor of Name.ident * aml list
  | Tuple of aml list
