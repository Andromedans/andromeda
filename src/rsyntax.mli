(** Runtime syntax, suitable for evaluation. *)

type ml_constructor = Path.level

(** An operation is referred to by a unique identifier *)
type operation = Ident.t

(** A TT constructor is referred to by a unique identifier *)
type tt_constructor = Ident.t

(** Runtime code keeps around locations of the source code that it was generated
    from, so that we can print informative runtime error messages. *)
type 'a located = 'a Location.located

module Pattern :
sig
(** Judgement pattern. *)
  type judgement = judgement' located
  and judgement' =
    | TTAnonymous
    | TTVar
    | TTAs of judgement * judgement
    | TTConstructor of tt_constructor * argument list
    | TTGenAtom of is_term
    | TTIsType of is_type
    | TTIsTerm of is_term * is_type
    | TTEqType of is_type * is_type
    | TTEqTerm of is_term * is_term * is_type
    | TTAbstract of Name.t option * is_type * judgement

  and is_type = judgement
  and is_term = judgement
  and argument = judgement

  (** ML pattern *)
  type aml = aml' located
  and aml' =
    | Anonymous
    | Var
    | As of aml * aml
    | Judgement of judgement
    | MLConstructor of ml_constructor * aml list
    | Tuple of aml list
end

(** Computations *)
type comp = comp' located
and comp' =
  | Bound of Path.index
  | Value of Path.t
  | Function of comp
  | Handler of handler
  | MLConstructor of ml_constructor * comp list
  | Tuple of comp list
  | Operation of operation * comp list
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
  | IsTypeConstructor of tt_constructor * comp list
  | IsTermConstructor of tt_constructor * comp list
  | EqTypeConstructor of tt_constructor * comp list
  | EqTermConstructor of tt_constructor * comp list
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

(** A let-clause is given by a list of variables that get bound with their
   types, a pattern that binds these variables (so the variables list needs to
   match the pattern!), and the body of the definition. *)
and let_clause =
  | Let_clause of (Name.t * Mlty.ty_schema) list * Pattern.aml * comp

and letrec_clause =
  | Letrec_clause of Name.t * Name.t * Mlty.ty_schema * comp

and handler = {
  handler_val: match_case list;
  handler_ops: match_op_case list Ident.map;
  handler_finally : match_case list;
}

and match_case = Pattern.aml * comp option * comp

(** Match multiple patterns at once, with shared pattern variables *)
and match_op_case = Pattern.aml list * Pattern.judgement option * comp

(** Type definitions are needed during runtime so that we can print them
    at the toplevel. *)
type ml_tydef =
  | ML_Sum of (Name.t * Mlty.ty list) list
  | ML_Alias of Mlty.ty

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
  | RuleIsType of tt_constructor * premise list
  | RuleIsTerm of tt_constructor * premise list * comp
  | RuleEqType of tt_constructor * premise list * (comp * comp)
  | RuleEqTerm of tt_constructor * premise list * (comp * comp * comp)
  | DefMLType of Name.t list (* we only need the names *)
  | DefMLTypeRec of Name.t list
  | DeclOperation of Name.t * (Mlty.ty list * Mlty.ty)
  | DeclExternal of Name.t * Mlty.ty_schema * string
  | TopLet of let_clause list
  | TopLetRec of letrec_clause list
  | TopComputation of comp * Mlty.ty_schema
  | TopDynamic of Name.t * Mlty.ty_schema * comp
  | TopNow of comp * comp
  | Verbosity of int
  | MLModule of Name.t * toplevel list
