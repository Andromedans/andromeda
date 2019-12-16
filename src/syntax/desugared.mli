(** Desugared input syntax *)

type 'a located = 'a Location.located

type ml_ty = ml_ty' located
and ml_ty' =
  | ML_Arrow of ml_ty * ml_ty
  | ML_Prod of ml_ty list
  | ML_Apply of Path.t * ml_ty list
  | ML_Handler of ml_ty * ml_ty
  | ML_Ref of ml_ty
  | ML_Exn
  | ML_Judgement
  | ML_Boundary
  | ML_Derivation
  | ML_String
  | ML_Bound of Path.index
  | ML_Anonymous

type ml_schema = ml_schema' located
and ml_schema' = ML_Forall of Name.t option list * ml_ty

type arg_annotation =
  | Arg_annot_none
  | Arg_annot_ty of ml_ty

type let_annotation =
  | Let_annot_none
  | Let_annot_schema of ml_schema

type pattern = pattern' located
and pattern' =
  | Patt_Anonymous
  | Patt_Var of Name.t
  | Patt_MLAscribe of pattern * ml_ty
  | Patt_As of pattern * pattern
  | Patt_TTConstructor of Path.t * pattern list
  | Patt_GenAtom of pattern
  | Patt_IsType of pattern
  | Patt_IsTerm of pattern * pattern
  | Patt_EqType of pattern * pattern
  | Patt_EqTerm of pattern * pattern * pattern
  | Patt_Abstraction of Name.t option * pattern * pattern
  | Patt_BoundaryIsType
  | Patt_BoundaryIsTerm of pattern
  | Patt_BoundaryEqType of pattern * pattern
  | Patt_BoundaryEqTerm of pattern * pattern * pattern
  | Patt_MLConstructor of Path.ml_constructor * pattern list
  | Patt_MLException of Path.t * pattern option
  | Patt_Tuple of pattern list
  | Patt_String of string

(** Desugared computations *)
type comp = comp' located
and comp' =
  | Bound of Path.index
  | Value of Path.t
  | Function of Name.t * arg_annotation * comp
  | Handler of handler
  | MLConstructor of Path.ml_constructor * comp list
  | Tuple of comp list
  | Operation of Path.t * comp list
  | With of comp * comp
  | MLException of Path.t * comp option
  | Raise of comp
  | Let of let_clause list * comp
  | LetRec of letrec_clause list * comp
  | MLAscribe of comp * ml_schema
  | Lookup of comp
  | Update of comp * comp
  | Ref of comp
  | Sequence of comp * comp
  | Fresh of Name.t option * comp
  | Match of comp * match_case list
  | BoundaryAscribe of comp * comp
  | TypeAscribe of comp * comp
  | TTConstructor of Path.t * comp list
  | Spine of comp * comp list
  | Abstract of Name.t * comp option * comp
  | AbstractAtom of comp * comp
  | Substitute of comp * comp
  | Derive of premise list * comp
  | String of string
  | Occurs of comp * comp
  | Congruence of comp * comp * comp list
  | Convert of comp * comp
  | Context of comp
  | Natural of comp
  | MLBoundary of boundary

and boundary =
  | BoundaryIsType
  | BoundaryIsTerm of comp
  | BoundaryEqType of comp * comp
  | BoundaryEqTerm of comp * comp * comp

and let_clause =
  | Let_clause of pattern * let_annotation * comp (* [let (?p :> t) = c] *)

and letrec_clause =
  | Letrec_clause of Name.t * (Name.t * arg_annotation) * let_annotation * comp

and handler = {
  handler_val: match_case list ;
  handler_ops: (Path.t * match_op_case list) list ;
  handler_exc : exception_case list
}

and match_case = pattern * comp option * comp

and exception_case = match_case

and top_operation_case = Path.t * match_op_case

(** Match multiple patterns at once, with shared pattern variables *)
and match_op_case = pattern list * pattern option * comp

and local_context = (Name.t * comp) list

and premise = premise' located
and premise' = Premise of Name.t * local_context * boundary

type ml_tydef =
  | ML_Sum of (Name.t * ml_ty list) list
  | ML_Alias of ml_ty

(** Desugared toplevel commands *)
type toplevel = toplevel' located
and toplevel' =
  | Rule of Path.t * premise list * boundary
  | DefMLTypeAbstract of Path.t * Name.t option list
  | DefMLType of (Path.t * (Name.t option list * ml_tydef)) list
  | DefMLTypeRec of (Path.t * (Name.t option list * ml_tydef)) list
  | DeclOperation of Path.t * (ml_ty list * ml_ty)
  | DeclException of Path.t * ml_ty option
  | DeclExternal of Name.t * ml_schema * string
  | TopLet of let_clause list
  | TopLetRec of letrec_clause list
  | TopWith of top_operation_case list
  | TopComputation of comp
  | Verbosity of int
  | Open of Path.t
  | MLModule of Name.t * toplevel list
