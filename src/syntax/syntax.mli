(** Runtime syntax, suitable for evaluation. *)

type ml_constructor = Ident.t

(** An operation is referred to by a unique identifier *)
type operation = Ident.t

(** An exception is referred to by a unique identifier *)
type ml_exception = Ident.t

(** An exception is referred to by a unique identifier *)
type exc = Ident.t

(** A rule/constructor is referred to by a unique identifier *)
type tt_constructor = Ident.t

(** Runtime code keeps around locations of the source code that it was generated
    from, so that we can print informative runtime error messages. *)
type 'a located = 'a Location.located

type pattern = pattern' located
and pattern' =
  | Patt_Anonymous
  | Patt_Var
  | Patt_As of pattern * pattern
  | Patt_TTConstructor of tt_constructor * pattern list
  | Patt_GenAtom of pattern
  | Patt_IsType of pattern
  | Patt_IsTerm of pattern * pattern
  | Patt_EqType of pattern * pattern
  | Patt_EqTerm of pattern * pattern * pattern
  | Patt_Abstract of Name.t option * pattern * pattern
  | Patt_BoundaryIsType
  | Patt_BoundaryIsTerm of pattern
  | Patt_BoundaryEqType of pattern * pattern
  | Patt_BoundaryEqTerm of pattern * pattern * pattern
  | Patt_MLException of exc * pattern option
  | Patt_MLConstructor of ml_constructor * pattern list
  | Patt_Tuple of pattern list
  | Patt_String of string

(** Computations *)
type comp = comp' located
and comp' =
  | Bound of Path.index
  | Value of Path.t
  | Function of comp
  | Handler of handler
  | MLConstructor of ml_constructor * comp list
  | Tuple of comp list
  | MLException of ml_exception * comp option
  | Operation of operation * comp list
  | With of comp * comp
  | Let of let_clause list * comp
  | LetRec of letrec_clause list * comp
  | Lookup of comp
  | Update of comp * comp
  | Ref of comp
  | Sequence of comp * comp
  | Raise of comp
  | Fresh of Name.t option * comp
  | Match of comp * match_case list
  | BoundaryAscribe of comp * comp
  | TypeAscribe of comp * comp
  | TTConstructor of tt_constructor * comp list
  | TTApply of comp * comp list
  | Apply of comp * comp
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
  | Let_clause of pattern * comp

and letrec_clause =
  | Letrec_clause of comp

and handler = {
  handler_val: match_case list ;
  handler_ops: match_op_case list Ident.map ;
  handler_exc : exception_case list
}

and exception_case = match_case

and match_case = pattern * comp option * comp

(** Match multiple patterns at once, with shared pattern variables *)
and match_op_case = pattern list * pattern option * comp

and local_context = (Name.t * comp) list

and premise = premise' located
and premise' = Premise of Name.t * local_context * boundary

(** Type definitions are needed during runtime so that we can print them
    at the toplevel. *)
type ml_tydef =
  | ML_Sum of (Name.t * Mlty.ty list) list
  | ML_Alias of Mlty.ty

(** Toplevel commands *)
type toplevel = toplevel' located
and toplevel' =
  | Rule of tt_constructor * premise list * boundary
  | DefMLType of Path.t list (* we only need the names *)
  | DefMLTypeRec of Path.t list
  | DeclOperation of Path.t * (Mlty.ty list * Mlty.ty)
  | DeclException of Path.t * Mlty.ty option
  | DeclExternal of Name.t * Mlty.ty_schema * string
  | TopLet of (Name.t * Mlty.ty_schema) list list * let_clause list
  | TopLetRec of (Name.t * Mlty.ty_schema) list * letrec_clause list
  | TopWith of (operation * match_op_case) list
  | TopComputation of comp * Mlty.ty_schema
  | Verbosity of int
  | Open of Path.t
  | MLModule of Name.t * toplevel list
