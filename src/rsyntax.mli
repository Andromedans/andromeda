(** Runtime syntax *)

(** Bound variables are de Bruijn indices *)
type bound = int

(** AML type declarations are referred to by de Bruijn levels *)
type level = int

type 'a located = 'a Location.located

type ml_ty = Mlty.ty

type ml_schema = Mlty.ty_schema

type arg_annotation =
  | Arg_annot_none
  | Arg_annot_ty of ml_ty

type let_annotation =
  | Let_annot_none
  | Let_annot_schema of ml_schema

(** Computations *)
type comp = comp' located
and comp' =
  | Bound of bound
  | Function of Name.ident * comp
  | Handler of handler
  | AMLConstructor of Name.ident * comp list
  | Tuple of comp list
  | Operation of Name.ident * comp list
  | With of comp * comp
  | Let of let_clause list * comp
  | LetRec of letrec_clause list * comp
  | Now of comp * comp * comp
  | Current of comp
  | Lookup of comp
  | Update of comp * comp
  | Ref of comp
  | Sequence of comp * comp
  | Assume of (Name.ident option * comp) * comp
  | Match of comp * match_case list
  | Ascribe of comp * comp
  | IsTypeConstructor of Name.constructor * comp list
  | IsTermConstructor of Name.constructor * comp list
  | EqTypeConstructor of Name.constructor * comp list
  | EqTermConstructor of Name.constructor * comp list
  | Apply of comp * comp
  | Abstract of Name.ident * comp option * comp
  | Substitute of comp * comp
  | Yield of comp
  | String of string
  | OccursIsTypeAbstraction of comp * comp
  | OccursIsTermAbstraction of comp * comp
  | OccursEqTypeAbstraction of comp * comp
  | OccursEqTermAbstraction of comp * comp
  | Context of comp
  | Natural of comp

and let_clause =
  | Let_clause of (Name.ident * ml_schema) list * Pattern.aml * comp

and letrec_clause =
  | Letrec_clause of Name.ident * Name.ident * ml_schema * comp

and handler = {
  handler_val: match_case list;
  handler_ops: match_op_case list Name.IdentMap.t;
  handler_finally : match_case list;
}

and match_case = Pattern.aml * comp option * comp

(** Match multiple patterns at once, with shared pattern variables *)
and match_op_case = Pattern.aml list * Pattern.judgement option * comp

type top_op_case = Name.ident list * Name.ident option * comp

type constructor_decl = Name.aml_constructor * ml_ty list

type ml_tydef = Dsyntax.ml_tydef

type local_context = (Name.ident * comp) list

type premise = premise' located
and premise' =
  | PremiseIsType of Name.ident option * local_context
  | PremiseIsTerm of Name.ident option * local_context * comp
  | PremiseEqType of Name.ident option * local_context * (comp * comp)
  | PremiseEqTerm of Name.ident option * local_context * (comp * comp * comp)

(** Toplevel commands *)
type toplevel = toplevel' located
and toplevel' =
  | RuleIsType of Name.ident * premise list
  | RuleIsTerm of Name.ident * premise list * comp
  | RuleEqType of Name.ident * premise list * (comp * comp)
  | RuleEqTerm of Name.ident * premise list * (comp * comp * comp)
  | DefMLType of (Name.ty * (Name.ty option list * ml_tydef)) list
  | DefMLTypeRec of (Name.ty * (Name.ty option list * ml_tydef)) list
  | DeclOperation of Name.operation * (ml_ty list * ml_ty)
  | DeclExternal of Name.ident * ml_schema * string
  | TopHandle of (Name.operation * top_op_case) list
  | TopLet of let_clause list
  | TopLetRec of letrec_clause list
  | TopDynamic of Name.ident * ml_schema * comp
  | TopNow of comp * comp
  | Verbosity of int
  | Included of (string * toplevel list) list
