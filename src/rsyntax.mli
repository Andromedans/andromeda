(** Runtime syntax, suitable for evaluation. *)

type ml_constructor = Ident.t

(** An operation is referred to by a unique identifier *)
type operation = Ident.t

(** A rule/constructor is referred to by a unique identifier *)
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

  (** Boundary pattern *)
  type boundary = Boundary_Pattern_Not_Implemented

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
  | BoundaryAscribe of comp * comp
  | TTConstructor of tt_constructor * comp list
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

(** The boundary of the conclusion of a premise or a rule *)
and boundary =
   | BoundaryIsType
   | BoundaryIsTerm of comp
   | BoundaryEqType of comp * comp
   | BoundaryEqTerm of comp * comp * comp

(** A let-clause is given by a list of names with their types, a pattern that
   binds these variables (so the variables list needs to match the pattern!),
   and the body of the definition.

   The names and types are used only for printing during runtime. *)
and let_clause =
  | Let_clause of Pattern.aml * comp

and letrec_clause =
  | Letrec_clause of comp

and handler = {
  handler_val: match_case list;
  handler_ops: match_op_case list Ident.map;
  handler_finally : match_case list;
}

and match_case = Pattern.aml * comp option * comp

(** Match multiple patterns at once, with shared pattern variables *)
and match_op_case = Pattern.aml list * Pattern.boundary option * comp

(** Type definitions are needed during runtime so that we can print them
    at the toplevel. *)
type ml_tydef =
  | ML_Sum of (Name.t * Mlty.ty list) list
  | ML_Alias of Mlty.ty

type local_context = (Name.t * comp) list

type premise = premise' located
and premise' = Premise of Name.t * local_context * boundary

(** Toplevel commands *)
type toplevel = toplevel' located
and toplevel' =
  | Rule of tt_constructor * premise list * boundary
  | DefMLType of Path.t list (* we only need the names *)
  | DefMLTypeRec of Path.t list
  | DeclOperation of Path.t * (Mlty.ty list * Mlty.ty)
  | DeclExternal of Name.t * Mlty.ty_schema * string
  | TopLet of (Name.t * Mlty.ty_schema) list list * let_clause list
  | TopLetRec of (Name.t * Mlty.ty_schema) list * letrec_clause list
  | TopComputation of comp * Mlty.ty_schema
  | TopDynamic of Name.t * Mlty.ty_schema * comp
  | TopNow of comp * comp
  | Verbosity of int
  | Open of Path.t
  | MLModule of Name.t * toplevel list
