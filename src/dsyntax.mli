(** Desugared input syntax *)

type 'a located = 'a Location.located

type ml_ty = ml_ty' located
and ml_ty' =
  | ML_Arrow of ml_ty * ml_ty
  | ML_Prod of ml_ty list
  | ML_Apply of Path.t * ml_ty list
  | ML_Handler of ml_ty * ml_ty
  | ML_Ref of ml_ty
  | ML_Dynamic of ml_ty
  | ML_Judgement
  | ML_Boundary
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
  | Patt_Tuple of pattern list

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
  | Let of let_clause list * comp
  | LetRec of letrec_clause list * comp
  | MLAscribe of comp * ml_schema
  | Now of comp * comp * comp
  | Current of comp
  | Lookup of comp
  | Update of comp * comp
  | Ref of comp
  | Sequence of comp * comp
  | Assume of (Name.t option * comp) * comp
  | Match of comp * match_case list
  | BoundaryAscribe of comp * comp
  | TypeAscribe of comp * comp
  | TTConstructor of Path.t * comp list
  | Apply of comp * comp
  | Abstract of Name.t * comp option * comp
  | Substitute of comp * comp
  | Yield of comp
  | String of string
  | Occurs of comp * comp
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
  handler_val: match_case list;
  handler_ops: (Path.t * match_op_case list) list ;
  handler_finally : match_case list;
}

and match_case = pattern * comp option * comp

(** Match multiple patterns at once, with shared pattern variables *)
and match_op_case = pattern list * pattern option * comp

type ml_tydef =
  | ML_Sum of (Name.t * ml_ty list) list
  | ML_Alias of ml_ty

type local_context = (Name.t * comp) list

type premise = premise' located
and premise' = Premise of Name.t * local_context * boundary

(** Desugared toplevel commands *)
type toplevel = toplevel' located
and toplevel' =
  | Rule of Path.t * premise list * boundary
  | DefMLType of (Path.t * (Name.t option list * ml_tydef)) list
  | DefMLTypeRec of (Path.t * (Name.t option list * ml_tydef)) list
  | DeclOperation of Path.t * (ml_ty list * ml_ty)
  | DeclExternal of Name.t * ml_schema * string
  | TopLet of let_clause list
  | TopLetRec of letrec_clause list
  | TopComputation of comp
  | TopDynamic of Name.t * arg_annotation * comp
  | TopNow of comp * comp
  | Verbosity of int
  | Open of Path.t
  | MLModule of Name.t * toplevel list
