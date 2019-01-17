(** Runtime syntax *)

(** Bound values are referred to by de Bruijn indices *)
type bound = int

(** ML type declarations are referred to by de Bruijn levels *)
type ml_type = int

(** An ML constructor is referred to by its position in the type definition *)
type ml_constructor = int

type 'a located = 'a Location.located

type ml_schema = Mlty.ty_schema

type arg_annotation =
  | Arg_annot_none
  | Arg_annot_ty of Mlty.ty

type let_annotation =
  | Let_annot_none
  | Let_annot_schema of ml_schema

(** Computations *)
type comp = comp' located
and comp' =
  | Bound of bound
  | Function of comp
  | Handler of handler
  | MLConstructor of Path.t * comp list
  | Tuple of comp list
  | Operation of Path.t * comp list
  | With of comp * comp
  | Let of let_clause list * comp
  | LetRec of letrec_clause list * comp
  | Now of comp * comp * comp
  | Current of comp
  | Lookup of comp
  | Update of comp * comp
  | Ref of comp
  | Sequence of comp * comp
  | Assume of (Name.t option * comp) * comp
  | Match of comp * match_case list
  | Ascribe of comp * comp
  | IsTypeConstructor of Path.t * comp list
  | IsTermConstructor of Path.t * comp list
  | EqTypeConstructor of Path.t * comp list
  | EqTermConstructor of Path.t * comp list
  | Apply of comp * comp
  | Abstract of Name.t * comp option * comp
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
  | Let_clause of (Name.t * ml_schema) list * Pattern.aml * comp

and letrec_clause =
  | Letrec_clause of Name.t * Name.t * ml_schema * comp

and handler = {
  handler_val: match_case list;
  handler_ops: match_op_case list Ident.map;
  handler_finally : match_case list;
}

and match_case = Pattern.aml * comp option * comp

(** Match multiple patterns at once, with shared pattern variables *)
and match_op_case = Pattern.aml list * Pattern.judgement option * comp

type ml_tydef = Dsyntax.ml_tydef

type local_context = (Name.t * comp) list

type premise = premise' located
and premise' =
  | PremiseIsType of Name.t option * local_context
  | PremiseIsTerm of Name.t option * local_context * comp
  | PremiseEqType of Name.t option * local_context * (comp * comp)
  | PremiseEqTerm of Name.t option * local_context * (comp * comp * comp)

(** Toplevel commands *)
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
  | TopComputation of comp * ml_schema
  | TopDynamic of Name.t * ml_schema * comp
  | TopNow of comp * comp
  | Verbosity of int
  | MLModules of (Name.t * toplevel list) list
