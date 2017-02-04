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
  | ML_Ref of ml_ty
  | ML_Dynamic of ml_ty
  | ML_Judgment
  | ML_String
  | ML_Anonymous

type ml_schema = ml_schema' Location.located
and ml_schema' = ML_Forall of Name.ty list * ml_ty

(** Annotation of an ML-function argument *)
type arg_annotation =
  | Arg_annot_none
  | Arg_annot_ty of ml_ty

(** Annotation of a let-binding *)
type let_annotation =
  | Let_annot_none
  | Let_annot_schema of ml_schema

(** A binder in a pattern may or may not bind the bound variable
    as a pattern variable. *)
type tt_variable =
  | PattVar of Name.ident
  | NonPattVar of Name.ident

(* An argument of a function or a let-clause *)
type ml_arg = Name.ident * arg_annotation

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
  | Var of Name.ident
  | Type
  | Function of ml_arg list * comp
  | Handler of handle_case list
  | Handle of comp * handle_case list
  | With of expr * comp
  | List of comp list
  | Tuple of comp list
  | Match of comp * match_case list
  | Let of let_clause list  * comp
  | LetRec of letrec_clause list * comp
  | MLAscribe of comp * ml_schema
  | Now of comp * comp * comp
  | Current of comp
  | Lookup of comp
  | Update of comp * comp
  | Ref of comp
  | Sequence of comp * comp
  | Assume of (Name.ident * comp) * comp
  | Where of comp * expr * comp
  | Ascribe of comp * ty
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

and let_clause =
  | Let_clause_ML of Name.ident * ml_arg list * let_annotation * comp
  | Let_clause_tt of Name.ident * ty * comp
  | Let_clause_patt of pattern * let_annotation * comp


and letrec_clause = Name.ident * ml_arg * ml_arg list * let_annotation * comp

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
  | DeclExternal of Name.ident * ml_schema * string
  | TopHandle of (Name.ident * top_op_case) list
  | TopLet of let_clause list
  | TopLetRec of letrec_clause list
  | TopDynamic of Name.ident * arg_annotation * comp
  | TopNow of comp * comp
  | TopDo of comp (** evaluate a computation at top level *)
  | TopFail of comp
  | Verbosity of int
  | Require of string list
