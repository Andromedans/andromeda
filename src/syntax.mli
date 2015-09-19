(** Desugared input syntax *)

(** Bound variables - represented by de Bruijn indices *)
type bound = int

(** Desugared expressions *)
type expr = expr' * Location.t
and expr' =
  | Type
  | Bound of bound
  | Function of Name.ident * comp
  | Handler of handler

(** Desugared types - indistinguishable from expressions *)
and ty = expr

(** Desugared computations *)
and comp = comp' * Location.t
and comp' =
  | Return of expr
  | Operation of string * expr
  | With of expr * comp
  | Let of (Name.ident * comp) list * comp
  | Apply of expr * expr
  | Beta of (string list * comp) list * comp
  | Eta of (string list * comp) list * comp
  | Hint of (string list * comp) list * comp
  | Inhabit of (string list * comp) list * comp
  | Unhint of string list * comp
  | Ascribe of comp * ty
  | Whnf of comp
  | Typeof of comp
  | Constant of Name.ident * comp list
  | Lambda of (Name.ident * comp option) list * comp
  | Spine of expr * comp list (* spine arguments are computations because we want
                                 to evaluate in checking mode, once we know their types. *)
  | Prod of (Name.ident * ty) list * comp (* XXX turn the ty into comp *)
  | Eq of comp * comp
  | Refl of comp
  | Bracket of comp
  | Inhab

and handler = {
  handler_val: (Name.ident * comp) option;
  handler_ops: (string * (Name.ident * Name.ident * comp)) list;
  handler_finally : (Name.ident * comp) option;
}

(** Desugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Axiom of Name.ident * (Name.ident * bool * comp) list * comp (** introduce a constant *)
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

