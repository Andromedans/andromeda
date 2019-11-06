(** Sugared input syntax

    The abstract syntax of input as typed by the user. At this stage
    there is no distinction between computations, expressions, and types.
    However, we define type aliases for these for better readability.
    There are no de Bruijn indices either. *)

type 'a located = 'a Location.located

(** Bound variables are de Bruijn indices *)
type bound = int

type path = Name.path

type ml_ty = ml_ty' located
and ml_ty' =
  | ML_Arrow of ml_ty * ml_ty
  | ML_Prod of ml_ty list
  | ML_TyApply of path * ml_ty list
  | ML_Handler of ml_ty * ml_ty
  | ML_Ref of ml_ty
  | ML_Dynamic of ml_ty
  | ML_Judgement
  | ML_Boundary
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

(** Sugared patterns *)
type pattern = pattern' located
and pattern' =
  | Patt_Anonymous
  | Patt_Path of Name.path
  | Patt_MLAscribe of pattern * ml_ty
  | Patt_As of pattern * pattern
  | Patt_GenAtom of pattern
  | Patt_IsType of pattern
  | Patt_IsTerm of pattern * pattern
  | Patt_EqType of pattern * pattern
  | Patt_EqTerm of pattern * pattern * pattern
  | Patt_Abstraction of (Name.t option * pattern option) list * pattern
  | Patt_BoundaryIsType
  | Patt_BoundaryIsTerm of pattern
  | Patt_BoundaryEqType of pattern * pattern
  | Patt_BoundaryEqTerm of pattern * pattern * pattern
  | Patt_Constructor of path * pattern list
  | Patt_List of pattern list
  | Patt_Tuple of pattern list

(** Sugared terms *)
type comp = comp' located
and comp' =
  | Name of path
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
  | Fresh of Name.t option * comp
  | BoundaryAscribe of comp * comp
  | TypeAscribe of comp * comp
  | Abstract of (Name.t * comp option) list * comp
  (* Multi-argument substitutions are *not* treated as parallel substitutions
     but desugared to consecutive substitutions. *)
  | AbstractAtom of comp * comp
  | Substitute of comp * comp list
  | Spine of comp * comp list
  | Yield of comp
  | String of string
  | Congruence of Name.path * comp * comp * comp list
  | Context of comp
  | Convert of comp * comp
  | Occurs of comp * comp
  | Natural of comp
  | MLBoundaryIsType
  | MLBoundaryIsTerm of comp
  | MLBoundaryEqType of comp * comp
  | MLBoundaryEqTerm of comp * comp * comp

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
  | CaseOp of path * match_op_case (* op p1 ... pn -> c *)
  | CaseFinally of match_case (* finally p -> c *)

and match_case = pattern * comp option * comp

and match_op_case = pattern list * pattern option * comp

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
  | Include of path
  | Open of path
  | TopModule of Name.t * toplevel list
