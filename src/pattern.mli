(** Patterns are common to desugared syntax and runtime syntax. *)

type 'a located = 'a Location.located

(** Bound variables are de Bruijn indices *)
type bound = int


(** Type pattern *)
type is_term_pattern = is_term_pattern' located
and is_term_pattern' =
  | Term_Anonymous
  | Term_As of is_term_pattern * bound
  | Term_Bound of bound
  | Term_Type
  | Term_Constant of Name.ident
  | Term_Lambda of Name.ident * bound option * is_type_pattern option * is_term_pattern
  | Term_Apply of is_term_pattern * is_term_pattern
  | Term_Refl of is_term_pattern
  | Term_GenAtom of is_term_pattern
  | Term_GenConstant of is_term_pattern

and is_type_pattern = is_type_pattern' located
and is_type_pattern' =
  | Tt_Prod of Name.ident * bound option * is_type_pattern option * is_type_pattern
  | Tt_Eq of is_type_pattern * is_type_pattern

type eq_term = eq_term' located
and eq_term' = is_term_pattern * is_term_pattern * is_type_pattern

type eq_type = eq_type' located
and eq_type' = is_type_pattern * is_type_pattern

(** AML pattern *)
type pattern = pattern' located
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * bound
  | Patt_Bound of bound
  | Patt_Jdg of tt_pattern * tt_pattern
  | Patt_Constructor of Name.ident * pattern list
  | Patt_Tuple of pattern list
