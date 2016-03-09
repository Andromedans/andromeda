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
  (** Generic matching *)
  | Tt_GenSig of pattern
  | Tt_GenStruct of tt_pattern * pattern
  | Tt_GenProj of tt_pattern * pattern
  | Tt_GenAtom of tt_pattern
  | Tt_GenConstant of tt_pattern

and pattern = pattern' * Location.t
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * Name.ident
  | Patt_Var of Name.ident
  | Patt_Name of Name.ident
  | Patt_Jdg of tt_pattern * tt_pattern
  | Patt_Data of Name.ident * pattern list
  | Patt_List of pattern list
  | Patt_Tuple of pattern list

(** Sugared terms *)
type term = term' * Location.t
and term' =
  (* expressions *)
  | Var of Name.ident
  | Type
  | Function of Name.ident list * comp
  | Handler of handle_case list
  (* computations *)
  | Handle of comp * handle_case list
  | With of expr * comp
  | List of comp list
  | Tuple of comp list
  | Match of comp * match_case list
  | Let of let_clause list  * comp
  | LetRec of letrec_clause list * comp
  | Now of Name.ident * comp * comp
  | Lookup of comp
  | Update of comp * comp
  | Ref of comp
  | Sequence of comp * comp
  | Assume of (Name.ident * comp) * comp
  | Where of comp * expr * comp
  | Ascribe of comp * ty
  | External of string
  | Lambda of (Name.ident * comp option) list * comp
  | Spine of comp * comp list
  | Prod of (Name.ident * ty) list * comp
  | Eq of comp * comp
  | Refl of comp
  | Signature of Name.signature * (Name.label * Name.ident option * comp option) list
  | Structure of (Name.label * Name.ident option * comp option) list
  | Projection of comp * Name.label
  | Yield of comp
  | Hypotheses
  | Congruence of comp * comp
  | Extensionality of comp * comp
  | Reduction of comp
  | String of string
  | GenSig of comp * comp
  | GenStruct of comp * comp
  | GenProj of comp * comp
  | Context of comp
  | Occurs of comp * comp
  | Ident of Name.ident

(** Sugared types *)
and ty = term

(** Sugared computations *)
and comp = term

(** Sugared expressions *)
and expr = term

and let_clause = Name.ident * Name.ident list * ty option * comp

and letrec_clause = Name.ident * Name.ident * Name.ident list * ty option * comp

(** Handle cases *)
and handle_case =
  | CaseVal of match_case (* val p -> c *)
  | CaseOp of Name.ident * match_op_case (* op p1 ... pn -> c *)
  | CaseFinally of match_case (* finally p -> c *)

and match_case = pattern * comp

and match_op_case = pattern list * pattern option * comp

type top_op_case = Name.ident list * Name.ident option * comp

type aml_ty = aml_ty' * Location.t
and aml_ty' =
  | AML_ty_Arrow of aml_ty * aml_ty
  | AML_ty_Prod of aml_ty list
  | AML_ty_Apply of Name.ty * aml_ty list
  | AML_ty_Handler of aml_ty * aml_ty
  | AML_ty_Judgement

type aml_schema = Forall of Name.ty list * aml_ty

type decl_constructor = Name.constructor * aml_ty list

(** Sugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | DeclType of Name.ty * Name.ty list * decl_constructor list
  | DeclOperation of Name.ident * Name.ty list * aml_ty list * aml_ty
  | DeclConstants of Name.ident list * ty
  | DeclSignature of Name.signature * (Name.label * Name.ident option * ty) list
  | TopHandle of (Name.ident * top_op_case) list
  | TopLet of let_clause list
  | TopLetRec of letrec_clause list
  | TopDynamic of Name.ident * comp
  | TopNow of Name.ident * comp
  | TopDo of comp (** evaluate a computation at top level *)
  | TopFail of comp
  | Verbosity of int
  | Include of string list * bool
    (** the boolean is [true] if the files should be included only once *)
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Environment (** print the current environment *)

