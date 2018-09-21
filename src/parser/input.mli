(** Sugared input syntax

    The abstract syntax of input as typed by the user. At this stage
    there is no distinction between computations, expressions, and types.
    However, we define type aliases for these for better readability.
    There are no de Bruijn indices either. *)

type 'a located = 'a Location.located

(** Bound variables are de Bruijn indices *)
type bound = int

type ml_abstraction =
  | ML_NotAbstract
  | ML_Abstract of ml_abstraction

type ml_ty = ml_ty' located
and ml_ty' =
  | ML_Arrow of ml_ty * ml_ty
  | ML_Prod of ml_ty list
  | ML_TyApply of Name.ty * ml_ty list
  | ML_Handler of ml_ty * ml_ty
  | ML_Ref of ml_ty
  | ML_Dynamic of ml_ty
  | ML_IsType of ml_abstraction
  | ML_IsTerm of ml_abstraction
  | ML_EqType of ml_abstraction
  | ML_EqTerm of ml_abstraction
  | ML_String
  | ML_Anonymous

type ml_schema = ml_schema' located
and ml_schema' = ML_Forall of Name.ty list * ml_ty

(** Annotation of an ML-function argument *)
type arg_annotation =
  | Arg_annot_none
  | Arg_annot_ty of ml_ty

(** Annotation of a let-binding *)
type let_annotation =
  | Let_annot_none
  | Let_annot_schema of ml_schema

(* An argument of a function or a let-clause *)
type ml_arg = Name.ident * arg_annotation

(** A binder in a pattern may or may not bind the bound variable
    as a pattern variable. *)
type tt_variable =
  | PattVar of Name.ident
  | NonPattVar of Name.ident

(** Sugared term patterns *)
type tt_pattern = tt_pattern' located
and tt_pattern' =
  | Patt_TT_Anonymous
  | Patt_TT_Var of Name.ident (* pattern variable *)
  | Patt_TT_Interpolate of Name.ident (* interpolated value *)
  | Patt_TT_As of tt_pattern * tt_pattern
  | Patt_TT_Constructor of Name.ident * tt_pattern list
  | Patt_TT_GenAtom of tt_pattern
  | Patt_TT_IsTerm of tt_pattern * tt_pattern
  | Patt_TT_EqType of tt_pattern * tt_pattern
  | Patt_TT_EqTerm of tt_pattern * tt_pattern * tt_pattern
  | Patt_TT_Abstraction of (tt_variable * tt_pattern option) list * tt_pattern

type pattern = pattern' located
and pattern' =
  | Patt_Anonymous
  | Patt_Var of Name.ident
  | Patt_Interpolate of Name.ident
  | Patt_As of pattern * pattern
  | Patt_Judgement of tt_pattern
  | Patt_Constr of Name.ident * pattern list
  | Patt_List of pattern list
  | Patt_Tuple of pattern list

(** Sugared terms *)
type term = term' located
and term' =
  | Var of Name.ident
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
  | Abstract of (Name.ident * comp option) list * comp
  | Spine of comp * comp list
  | Yield of comp
  | CongrAbstractTy of comp * comp * comp
  | CongrAbstract of comp * comp * comp * comp
  | Reflexivity_type of comp
  | Symmetry_type of comp
  | Transitivity_type of comp * comp
  | Reflexivity_term of comp
  | Symmetry_term of comp
  | Transitivity_term of comp * comp
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

type constructor_decl = Name.aml_constructor * ml_ty list

type ml_tydef =
  | ML_Sum of constructor_decl list
  | ML_Alias of ml_ty

(** Sugared toplevel commands *)
type toplevel = toplevel' located
and toplevel' =
  | DefMLType of (Name.ty * (Name.ty list * ml_tydef)) list
  | DefMLTypeRec of (Name.ty * (Name.ty list * ml_tydef)) list
  | DeclOperation of Name.ident * (ml_ty list * ml_ty)
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
