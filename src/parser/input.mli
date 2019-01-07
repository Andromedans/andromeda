(** Sugared input syntax

    The abstract syntax of input as typed by the user. At this stage
    there is no distinction between computations, expressions, and types.
    However, we define type aliases for these for better readability.
    There are no de Bruijn indices either. *)

type 'a located = 'a Location.located

(** Bound variables are de Bruijn indices *)
type bound = int

type ml_judgement =
  | ML_IsType
  | ML_IsTerm
  | ML_EqType
  | ML_EqTerm

type ml_abstracted_judgement =
  | ML_NotAbstract of ml_judgement
  | ML_Abstract of ml_abstracted_judgement

type ml_ty = ml_ty' located
and ml_ty' =
  | ML_Arrow of ml_ty * ml_ty
  | ML_Prod of ml_ty list
  | ML_TyApply of Name.path * ml_ty list
  | ML_Handler of ml_ty * ml_ty
  | ML_Ref of ml_ty
  | ML_Dynamic of ml_ty
  | ML_Judgement of ml_abstracted_judgement
  | ML_String
  | ML_Anonymous

type ml_schema = ml_schema' located
and ml_schema' = ML_Forall of Name.t option list * ml_ty

(** Annotation of an ML-function argument *)
type arg_annotation =
  | Arg_annot_none
  | Arg_annot_ty of ml_ty

(** Annotation of a let-binding *)
type let_annotation =
  | Let_annot_none
  | Let_annot_schema of ml_schema

(* An argument of a function or a let-clause *)
type ml_arg = Name.t * arg_annotation

(** Sugared term patterns *)
type tt_pattern = tt_pattern' located
and tt_pattern' =
  | Patt_TT_Anonymous
  | Patt_TT_Var of Name.t (* pattern variable *)
  | Patt_TT_As of tt_pattern * tt_pattern
  | Patt_TT_Constructor of Name.path * tt_pattern list
  | Patt_TT_GenAtom of tt_pattern
  | Patt_TT_IsType of tt_pattern
  | Patt_TT_IsTerm of tt_pattern * tt_pattern
  | Patt_TT_EqType of tt_pattern * tt_pattern
  | Patt_TT_EqTerm of tt_pattern * tt_pattern * tt_pattern
  | Patt_TT_Abstraction of (Name.t option * tt_pattern option) list * tt_pattern

type pattern = pattern' located
and pattern' =
  | Patt_Anonymous
  | Patt_Var of Name.t
  | Patt_As of pattern * pattern
  | Patt_Judgement of tt_pattern
  | Patt_Constructor of Name.path * pattern list
  | Patt_List of pattern list
  | Patt_Tuple of pattern list

(** Sugared terms *)
type comp = comp' located
and comp' =
  | Open of Name.t * comp
  | Var of Name.path
  | Function of ml_arg list * comp
  | Handler of handle_case list
  | Handle of comp * handle_case list
  | With of comp * comp
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
  | Assume of (Name.t option * comp) * comp
  | Ascribe of comp * comp
  | Abstract of (Name.t * comp option) list * comp
  (* Multi-argument substitutions are *not* treated as parallel substitutions
     but desugared to consecutive substitutions. *)
  | Substitute of comp * comp list
  | Spine of comp * comp list
  | Yield of comp
  | String of string
  | Context of comp
  | Occurs of comp * comp
  | Natural of comp

and let_clause =
  | Let_clause_ML of (Name.t * ml_arg list) option * let_annotation * comp
  | Let_clause_tt of Name.t option * comp * comp
  | Let_clause_patt of pattern * let_annotation * comp

(* XXX we should be able to destruct the first argument of a recursive function with an
   (irrefutable) pattern. Thus, [ml_arg] should be defined using patterns in place of variable names. *)
and letrec_clause = Name.t * ml_arg * ml_arg list * let_annotation * comp

(** Handle cases *)
and handle_case =
  | CaseVal of match_case (* val p -> c *)
  | CaseOp of Name.path * match_op_case (* op p1 ... pn -> c *)
  | CaseFinally of match_case (* finally p -> c *)

and match_case = pattern * comp option * comp

and match_op_case = pattern list * tt_pattern option * comp

type ml_tydef =
  | ML_Sum of (Name.t * ml_ty list) list
  | ML_Alias of ml_ty

(** The local context of a premise to a rule. *)
type local_context = (Name.t * comp) list

(** A premise to a rule *)
type premise = premise' located
and premise' =
  | PremiseIsType of Name.t option * local_context
  | PremiseIsTerm of Name.t option * local_context * comp
  | PremiseEqType of Name.t option * local_context * (comp * comp)
  | PremiseEqTerm of Name.t option * local_context * (comp * comp * comp)

(** Sugared toplevel commands *)
type toplevel = toplevel' located
and toplevel' =
  | RuleIsType of Name.t * premise list
  | RuleIsTerm of Name.t * premise list * comp
  | RuleEqType of Name.t * premise list * (comp * comp)
  | RuleEqTerm of Name.t * premise list * (comp * comp * comp)
  | DefMLType of (Name.t * (Name.t option list * ml_tydef)) list
  | DefMLTypeRec of (Name.t * (Name.t option list * ml_tydef)) list
  | DeclOperation of Name.t * (ml_ty list * ml_ty)
  | DeclExternal of Name.t * ml_schema * string
  | TopLet of let_clause list
  | TopLetRec of letrec_clause list
  | TopComputation of comp
  | TopDynamic of Name.t * arg_annotation * comp
  | TopNow of comp * comp
  | Verbosity of int
  | Require of Name.t list
