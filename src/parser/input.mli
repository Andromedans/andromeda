(** Sugared input syntax

    The abstract syntax of input as typed by the user. At this stage
    there is no distinction between computations, expressions, and types.
    However, we define type aliases for these for better readability.
    There are no de Bruijn indices either. *)

(** Sugared term patterns *)
type tt_pattern = tt_pattern' * Location.t
and tt_pattern' =
  | Tt_Anonymous
  | Tt_As of tt_pattern * Name.ident
  | Tt_Var of Name.ident
  | Tt_Type
  | Tt_Name of Name.ident
  (** For each binder the boolean indicates whether the bound variable should be a pattern variable *)
  | Tt_Lambda of bool * Name.ident * tt_pattern option * tt_pattern
  | Tt_App of tt_pattern * tt_pattern
  | Tt_Prod of bool * Name.ident * tt_pattern option * tt_pattern
  | Tt_Eq of tt_pattern * tt_pattern
  | Tt_Refl of tt_pattern
  | Tt_Signature of (Name.ident * bool * Name.ident option * tt_pattern) list
  | Tt_Structure of (Name.ident * bool * Name.ident option * tt_pattern) list
  | Tt_Projection of tt_pattern * Name.ident

type pattern = pattern' * Location.t
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * Name.ident
  | Patt_Var of Name.ident
  | Patt_Name of Name.ident
  | Patt_Jdg of tt_pattern * tt_pattern
  | Patt_Tag of Name.ident * pattern list

(** Sugared terms *)
type term = term' * Location.t
and term' =
  (* expressions *)
  | Var of Name.ident
  | Type
  | Function of Name.ident list * comp
  | Rec of Name.ident * Name.ident list * comp
  | Handler of handle_case list
  (* computations *)
  | Operation of string * expr
  | Handle of comp * handle_case list
  | With of expr * comp
  | Tag of Name.ident * comp list
  | Match of comp * match_case list
  | Let of (Name.ident * comp) list * comp
  | Assume of (Name.ident * comp) * comp
  | Where of comp * expr * comp
  | Beta of (string list * comp) list * comp
  | Eta of (string list * comp) list * comp
  | Hint of (string list * comp) list * comp
  | Unhint of string list * comp
  | Ascribe of comp * ty
  | Whnf of comp
  | Reduce of comp
  | External of string
  | Typeof of comp
  | Lambda of (Name.ident * comp option) list * comp
  | Spine of comp * comp list
  | Prod of (Name.ident * ty) list * comp
  | Eq of comp * comp
  | Refl of comp
  | Signature of (Name.ident * Name.ident option * ty) list
  | Structure of (Name.ident * Name.ident option * comp) list
  | Projection of comp * Name.ident
  | Yield
  | Context
  | Congruence of comp * comp

(** Sugared types *)
and ty = term

(** Sugared computations *)
and comp = term

(** Sugared expressions *)
and expr = term

(** Handle cases *)
and handle_case =
  | CaseVal of pattern * comp (* val p -> c *)
  | CaseOp of string * pattern * comp (* #op p -> c *)
  | CaseFinally of pattern * comp (* finally p -> c *)
                                  
and match_case = pattern * comp

(** Sugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Axiom of Name.ident * (bool * (Name.ident * ty)) list * ty
    (** introduce a primitive constant, the boolean is [true] if the argument is eagerly reducing *)
  | TopHandle of (string * Name.ident * comp) list 
  | TopLet of Name.ident * (Name.ident * ty) list * ty option * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | TopBeta of (string list * comp) list (** global beta hint *)
  | TopEta of (string list * comp) list (** global eta hint *)
  | TopHint of (string list * comp) list (** global hint *)
  | TopUnhint of string list
  | Verbosity of int
  | Include of string list
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Environment (** print the current environment *)
