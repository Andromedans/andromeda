(** Patterns are common to desugared syntax and runtime syntax. *)

type 'a located = 'a Location.located

(** Bound variables are de Bruijn indices *)
type bound = int


(** Patterns *)
type tt_pattern = tt_pattern' located
and tt_pattern' =
  | Tt_Anonymous
  | Tt_As of tt_pattern * bound
  | Tt_Bound of bound
  | Tt_Type
  | Tt_Constant of Name.ident
  | Tt_Lambda of Name.ident * bound option * tt_pattern option * tt_pattern
  | Tt_Apply of tt_pattern * tt_pattern
  | Tt_Prod of Name.ident * bound option * tt_pattern option * tt_pattern
  | Tt_Eq of tt_pattern * tt_pattern
  | Tt_Refl of tt_pattern
  | Tt_GenAtom of tt_pattern
  | Tt_GenConstant of tt_pattern

type pattern = pattern' located
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * bound
  | Patt_Bound of bound
  | Patt_Jdg of tt_pattern * tt_pattern
  | Patt_Constructor of Name.ident * pattern list
  | Patt_Tuple of pattern list
