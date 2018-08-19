(** Desugared input syntax *)

(** Bound variables are de Bruijn indices *)
type bound = int

(** AML type declarations are referred to by de Bruijn levels *)
type level = int

type 'a located = 'a Location.located

type ml_ty = ml_ty' located
and ml_ty' =
  | ML_Arrow of ml_ty * ml_ty
  | ML_Prod of ml_ty list
  | ML_TyApply of Name.ident * level * ml_ty list
  | ML_Handler of ml_ty * ml_ty
  | ML_Ref of ml_ty
  | ML_Dynamic of ml_ty
  | ML_IsType
  | ML_IsTerm
  | ML_EqType
  | ML_EqTerm
  | ML_String
  | ML_Bound of bound
  | ML_Anonymous

type ml_schema = ml_schema' located
and ml_schema' = ML_Forall of Name.ty list * ml_ty

type arg_annotation =
  | Arg_annot_none
  | Arg_annot_ty of ml_ty

type let_annotation =
  | Let_annot_none
  | Let_annot_schema of ml_schema

(** Desugared computations *)
type comp = comp' located
and comp' =
  | Type
  | El of comp
  | Bound of bound
  | Function of Name.ident * arg_annotation * comp
  | Handler of handler
  | Constructor of Name.ident * comp list
  | Tuple of comp list
  | Operation of Name.ident * comp list
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
  | Assume of (Name.ident * comp) * comp
  | Where of comp * comp * comp
  | Match of comp * match_case list
  | Ascribe of comp * comp
  | Constant of Name.ident
  | Apply of comp * comp
  | Abstract of Name.ident * comp option * comp
  | AbstractTy of Name.ident * comp * comp
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
  | Occurs of comp * comp
  | Context of comp
  | Natural of comp

and let_clause =
  | Let_clause_ML of Name.ident * let_annotation * comp
  | Let_clause_patt of Name.ident list * Pattern.aml * let_annotation * comp

and letrec_clause = Name.ident * (Name.ident * arg_annotation) * let_annotation * comp

and handler = {
  handler_val: match_case list;
  handler_ops: match_op_case list Name.IdentMap.t;
  handler_finally : match_case list;
}

and match_case = Name.ident list * Pattern.aml * comp

(** Match multiple patterns at once, with shared pattern variables *)
and match_op_case = Name.ident list * Pattern.aml list * Pattern.aml option * comp

type top_op_case = Name.ident list * Name.ident option * comp

type constructor_decl = Name.constructor * ml_ty list

type ml_tydef =
  | ML_Sum of constructor_decl list
  | ML_Alias of ml_ty

(** Desugared toplevel commands *)
type toplevel = toplevel' located
and toplevel' =
  | DefMLType of (Name.ty * (Name.ty list * ml_tydef)) list
  | DefMLTypeRec of (Name.ty * (Name.ty list * ml_tydef)) list
  | DeclOperation of Name.operation * (ml_ty list * ml_ty)
  | DeclConstants of Name.constant list * comp
  | DeclExternal of Name.ident * ml_schema * string
  | TopHandle of (Name.operation * top_op_case) list
  | TopLet of let_clause list
  | TopLetRec of letrec_clause list
  | TopDynamic of Name.ident * arg_annotation * comp
  | TopNow of comp * comp
  | TopDo of comp
  | TopFail of comp
  | Verbosity of int
  | Included of (string * toplevel list) list
