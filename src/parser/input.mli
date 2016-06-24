(** Sugared input syntax

    The abstract syntax of input as typed by the user. At this stage
    there is no distinction between computations, expressions, and types.
    However, we define type aliases for these for better readability.
    There are no de Bruijn indices either. *)

type ml_ty = ml_ty' Location.located
and ml_ty' =
  | ML_Arrow of ml_ty * ml_ty
  | ML_Prod of ml_ty list
  | ML_TyApply of Name.ty * ml_ty list
  | ML_Handler of ml_ty * ml_ty
  | ML_Judgment
  | ML_String
  | ML_Anonymous

type ml_schema = ml_schema' Location.located
and ml_schema' = ML_Forall of Name.ty list * ml_ty

(** A binder in a pattern may or may not bind the bound variable
    as a pattern variable. *)
type tt_variable =
  | PattVar of Name.ident
  | NonPattVar of Name.ident

(** Sugared term patterns *)
type tt_pattern = tt_pattern' Location.located
and tt_pattern' =
  | Tt_Anonymous
  | Tt_As of tt_pattern * Name.ident
  | Tt_Var of Name.ident (* pattern variable *)
  | Tt_Type
  | Tt_Name of Name.ident
  | Tt_Lambda of (tt_variable * tt_pattern option) list * tt_pattern
  | Tt_Spine of tt_pattern * tt_pattern list
  | Tt_Prod of (tt_variable * tt_pattern option) list * tt_pattern
  | Tt_Eq of tt_pattern * tt_pattern
  | Tt_Refl of tt_pattern
  | Tt_GenAtom of tt_pattern
  | Tt_GenConstant of tt_pattern

and pattern = pattern' Location.located
and pattern' =
  | Patt_Anonymous
  | Patt_As of pattern * Name.ident
  | Patt_Var of Name.ident
  | Patt_Name of Name.ident
  | Patt_Jdg of tt_pattern * tt_pattern option
  | Patt_Constr of Name.ident * pattern list
  | Patt_List of pattern list
  | Patt_Tuple of pattern list

(** Sugared terms *)
type term = term' Location.located
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
  | Yield of comp
  | CongrProd of comp * comp * comp
  | CongrApply of comp * comp * comp * comp * comp
  | CongrLambda of comp * comp * comp * comp
  | CongrEq of comp * comp * comp
  | CongrRefl of comp * comp
  | BetaStep of comp * comp * comp * comp * comp
  | String of string
  | Context of comp
  | Occurs of comp * comp
  | Natural of comp

(** Sugared types *)
and ty = term

(** Sugared computations *)
and comp = term

(** Sugared expressions *)
and expr = term

and let_clause = Name.ident * Name.ident list * ml_schema option * comp

and letrec_clause = Name.ident * Name.ident * Name.ident list * ml_schema option * comp

(** Handle cases *)
and handle_case =
  | CaseVal of match_case (* val p -> c *)
  | CaseOp of Name.ident * match_op_case (* op p1 ... pn -> c *)
  | CaseFinally of match_case (* finally p -> c *)

and match_case = pattern * comp

and match_op_case = pattern list * pattern option * comp

type top_op_case = Name.ident option list * Name.ident option * comp

type constructor_decl = Name.constructor * ml_ty list

type ml_tydef =
  | ML_Sum of constructor_decl list
  | ML_Alias of ml_ty

(** Sugared toplevel commands *)
type toplevel = toplevel' Location.located
and toplevel' =
  | DefMLType of (Name.ty * (Name.ty list * ml_tydef)) list
  | DefMLTypeRec of (Name.ty * (Name.ty list * ml_tydef)) list
  | DeclOperation of Name.ident * (ml_ty list * ml_ty)
  | DeclConstants of Name.ident list * ty
  | TopHandle of (Name.ident * top_op_case) list
  | TopLet of let_clause list
  | TopLetRec of letrec_clause list
  | TopDynamic of Name.ident * comp
  | TopNow of Name.ident * comp
  | TopDo of comp (** evaluate a computation at top level *)
  | TopFail of comp
  | Verbosity of int
  | Include of string list

