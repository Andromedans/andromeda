(** Sugared input syntax

    The abstract syntax of input as typed by the user. At this stage
    there is no distinction between computations, expressions, and types.
    However, we define type aliases for these for better readability.
    There are no de Bruijn indices either. *)

(** Sugared terms *)
type term = term' * Location.t
and term' =
  (* expressions *)
  | Var of Name.ident
  | Type
  | Function of Name.ident list * comp
  | Handler of handle_case list
  (* computations *)
  | Operation of string * expr
  | Handle of comp * handle_case list
  | With of expr * comp
  | Apply of expr * expr
  | Let of (Name.ident * comp) list * comp
  | Assume of (Name.ident * comp) * comp
  | Beta of (string list * comp) list * comp
  | Eta of (string list * comp) list * comp
  | Hint of (string list * comp) list * comp
  | Inhabit of (string list * comp) list * comp
  | Unhint of string list * comp
  | Ascribe of comp * ty
  | Whnf of comp
  | Typeof of comp
  | Lambda of (Name.ident * comp option) list * comp
  | Spine of comp * comp list
  | Prod of (Name.ident * ty) list * comp
  | Eq of comp * comp
  | Refl of comp
  | Bracket of comp
  | Inhab

(** Sugared types *)
and ty = term

(** Sugared computations *)
and comp = term

(** Sugared expressions *)
and expr = term

(** Handle cases *)
and handle_case =
  | CaseVal of Name.ident * comp (* val x -> c *)
  | CaseOp of string * Name.ident * Name.ident * comp (* #op x k -> c *)
  | CaseFinally of Name.ident * comp (* finally x -> c *)

(** Sugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Axiom of Name.ident * (bool * (Name.ident * ty)) list * ty (** introduce a primitive constant, the boolean is [true] if the argument is eagerly reducing *)
  | TopLet of Name.ident * (Name.ident * ty) list * ty option * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | TopBeta of (string list * comp) list (** global beta hint *)
  | TopEta of (string list * comp) list (** global eta hint *)
  | TopHint of (string list * comp) list (** global hint *)
  | TopInhabit of (string list * comp) list (** global inhabit hint *)
  | TopUnhint of string list
  | Verbosity of int
  | Include of string list
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Environment (** print the current environment *)
