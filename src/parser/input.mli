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
  | Tt_Var of Name.ident (* pattern variable *)
  | Tt_Type
  | Tt_Name of Name.ident
  (** For each binder the boolean indicates whether the bound variable
      should be a pattern variable *)
  | Tt_Lambda of bool * Name.ident * tt_pattern option * tt_pattern
  | Tt_Apply of tt_pattern * tt_pattern
  | Tt_Prod of bool * Name.ident * tt_pattern option * tt_pattern
  | Tt_Eq of tt_pattern * tt_pattern
  | Tt_Refl of tt_pattern
  | Tt_Structure of (Name.label * tt_pattern) list
  | Tt_Projection of tt_pattern * Name.ident

type pattern = pattern' * Location.t
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * Name.ident
  | Patt_Var of Name.ident
  | Patt_Name of Name.ident
  | Patt_Jdg of tt_pattern * tt_pattern
  | Patt_Data of Name.ident * pattern list
  | Patt_Cons of pattern * pattern
  | Patt_List of pattern list
  | Patt_Tuple of pattern list

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
  | Handle of comp * handle_case list
  | With of expr * comp
  | Cons of comp * comp
  | List of comp list
  | Tuple of comp list
  | Match of comp * match_case list
  | Let of (Name.ident * comp) list * comp
  | Lookup of comp
  | Update of comp * comp
  | Ref of comp
  | Sequence of comp * comp
  | Assume of (Name.ident * comp) * comp
  | Where of comp * expr * comp
  | Ascribe of comp * ty
  | Reduce of comp
  | External of string
  | Typeof of comp
  | Lambda of (Name.ident * comp option) list * comp
  | Spine of comp * comp list
  | Prod of (Name.ident * ty) list * comp
  | Eq of comp * comp
  | Refl of comp
  | Structure of (Name.ident * Name.ident option * comp) list
  | Projection of comp * Name.ident
  | Yield of comp
  | Context
  | Congruence of comp * comp
  | String of string

(** Sugared types *)
and ty = term

(** Sugared computations *)
and comp = term

(** Sugared expressions *)
and expr = term

(** Handle cases *)
and handle_case =
  | CaseVal of match_case (* val p -> c *)
  | CaseOp of Name.ident * multimatch_case (* op p1 ... pn -> c *)
  | CaseFinally of match_case (* finally p -> c *)

and match_case = pattern * comp

and multimatch_case = pattern list * comp

(** Sugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | DeclOperation of Name.ident * int
  | DeclData of Name.ident * int
  | DeclConstant of Name.ident * ty
  | DeclSignature of Name.signature * (Name.label * Name.ident option * ty) list
  | TopHandle of (Name.ident * Name.ident list * comp) list
  | TopLet of Name.ident * (Name.ident * ty) list * ty option * comp (** global let binding *)
  | TopDo of comp (** evaluate a computation at top level *)
  | TopFail of comp
  | Verbosity of int
  | Include of string list * bool
    (** the boolean is [true] if the files should be included only once *)
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Environment (** print the current environment *)
