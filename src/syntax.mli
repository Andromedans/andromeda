(** Desugared input syntax *)

(** Bound variables - represented by de Bruijn indices *)
type bound = int

(** Patterns *)

type tt_pattern = tt_pattern' * Location.t
and tt_pattern' =
  | Tt_Anonymous
  | Tt_Var of bound (* a pattern variable *)
  | Tt_Bound of bound
  | Tt_Type
  | Tt_Constant of Name.ident
  | Tt_Lambda of Name.ident * tt_pattern option * tt_pattern
  | Tt_App of tt_pattern * tt_pattern
  | Tt_Prod of Name.ident * tt_pattern option * tt_pattern
  | Tt_Eq of tt_pattern * tt_pattern
  | Tt_Refl of tt_pattern
  | Tt_Inhab
  | Tt_Bracket of tt_pattern
  | Tt_Signature of (Name.ident * Name.ident * tt_pattern) list
  | Tt_Structure of (Name.ident * Name.ident * tt_pattern) list
  | Tt_Projection of tt_pattern * Name.ident

type pattern = pattern' * Location.t
and pattern' =
  | Patt_Anonymous
  | Patt_Var of bound
  | Patt_Bound of bound
  | Patt_Jdg of tt_pattern * tt_pattern
  | Patt_Tag of Name.ident * pattern list

(** Desugared expressions *)
type expr = expr' * Location.t
and expr' =
  | Type
  | Bound of bound
  | Function of Name.ident * comp
  | Handler of handler
  | Tag of Name.ident * expr list

(** Desugared types - indistinguishable from expressions *)
and ty = expr

(** Desugared computations *)
and comp = comp' * Location.t
and comp' =
  | Return of expr
  | Operation of string * expr
  | With of expr * comp
  | Let of (Name.ident * comp) list * comp
  | Assume of (Name.ident * comp) * comp
  | Where of comp * expr * comp
  | Apply of expr * expr
  | Match of expr * match_case list
  | Beta of (string list * comp) list * comp
  | Eta of (string list * comp) list * comp
  | Hint of (string list * comp) list * comp
  | Inhabit of (string list * comp) list * comp
  | Unhint of string list * comp
  | Ascribe of comp * comp
  | Whnf of comp
  | Typeof of comp
  | Constant of Name.ident * comp list
  | Lambda of (Name.ident * comp option) list * comp
  | Spine of expr * comp list (* spine arguments are computations because we want
                                 to evaluate in checking mode, once we know their types. *)
  | Prod of (Name.ident * comp) list * comp
  | Eq of comp * comp
  | Refl of comp
  | Bracket of comp
  | Inhab
  | Signature of (Name.ident * Name.ident * comp) list
  | Structure of (Name.ident * Name.ident * comp) list
  | Projection of comp * Name.ident

and handler = {
  handler_val: (Name.ident * comp) option;
  handler_ops: (string * (Name.ident * Name.ident * comp)) list;
  handler_finally : (Name.ident * comp) option;
}

and match_case = Name.ident list * pattern * comp

(** Desugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Axiom of Name.ident * (bool * (Name.ident * comp)) list * comp (** introduce a constant *)
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

(** [shift_exp k lvl e] shifts the bound variables in computation [e] that
    are larger than or equal [lv] by [k]. *)
val shift_expr : int -> int -> expr -> expr

