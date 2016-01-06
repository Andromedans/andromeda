(** Desugared input syntax *)

(** Bound variables - represented by de Bruijn indices *)
type bound = int

(** Patterns *)

type tt_pattern = tt_pattern' * Location.t
and tt_pattern' =
  | Tt_Anonymous
  | Tt_As of tt_pattern * bound
  | Tt_Bound of bound
  | Tt_Type
  | Tt_Constant of Name.ident
  | Tt_Lambda of Name.ident * bound option * tt_pattern option * tt_pattern
  | Tt_App of tt_pattern * tt_pattern
  | Tt_Prod of Name.ident * bound option * tt_pattern option * tt_pattern
  | Tt_Eq of tt_pattern * tt_pattern
  | Tt_Refl of tt_pattern
  | Tt_Inhab
  | Tt_Bracket of tt_pattern
  | Tt_Signature of (Name.ident * Name.ident * bound option * tt_pattern) list
  | Tt_Structure of (Name.ident * Name.ident * bound option * tt_pattern) list
  | Tt_Projection of tt_pattern * Name.ident

type pattern = pattern' * Location.t
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * bound
  | Patt_Bound of bound
  | Patt_Jdg of tt_pattern * tt_pattern
  | Patt_Tag of Name.ident * pattern list

(** Desugared computations *)
type comp = comp' * Location.t
and comp' =
  | Type
  | Bound of bound
  | Function of Name.ident * comp
  | Rec of Name.ident * Name.ident * comp
  | Handler of handler
  | Tag of Name.ident * comp list
  | Operation of string * comp
  | With of comp * comp
  | Let of (Name.ident * comp) list * comp
  | Assume of (Name.ident * comp) * comp
  | Where of comp * comp * comp
  | Match of comp * match_case list
  | Beta of (string list * comp) list * comp
  | Eta of (string list * comp) list * comp
  | Hint of (string list * comp) list * comp
  | Inhabit of (string list * comp) list * comp
  | Unhint of string list * comp
  | Ascribe of comp * comp
  | Whnf of comp
  | External of string
  | Typeof of comp
  | Constant of Name.ident * comp list
  | Lambda of (Name.ident * comp option) list * comp
  | Spine of comp * comp list
  | Prod of (Name.ident * comp) list * comp
  | Eq of comp * comp
  | Refl of comp
  | Bracket of comp
  | Inhab
  | Signature of (Name.ident * Name.ident * comp) list
  | Structure of (Name.ident * Name.ident * comp) list
  | Projection of comp * Name.ident
  | Yield
  | Context

and handler = {
  handler_val: (Name.ident * comp) option;
  handler_ops: (string * (Name.ident * comp)) list;
  handler_finally : (Name.ident * comp) option;
}

and match_case = Name.ident list * pattern * comp

(** Desugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Axiom of Name.ident * (bool * (Name.ident * comp)) list * comp (** introduce a constant *)
  | TopHandle of (string * (Name.ident * comp)) list
  | TopLet of Name.ident * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | TopBeta of (string list * comp) list
  | TopEta of (string list * comp) list
  | TopHint of (string list * comp) list
  | TopInhabit of (string list * comp) list
  | TopUnhint of string list
  | Verbosity of int
  | Include of string list
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Environment (** print the current environment *)

(** [shift_comp k lvl c] shifts the bound variables in computation [c] that
    are larger than or equal [lv] by [k]. *)
val shift_comp : int -> int -> comp -> comp

