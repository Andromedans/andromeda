(** The datatypes for describing the user-definable rules of type theory. *)

(** Meta-variables appearing in rules are referred to by their de Bruijn _indices_. *)
type meta = int

type bound = int

type is_type =
  | TypeConstructor of Ident.t * argument list
  | TypeMeta of meta * is_term list

and is_term =
  | TermBound of bound
  | TermConstructor of Ident.t * argument list
  | TermMeta of meta * is_term list

and eq_type = EqType of is_type * is_type

and eq_term = EqTerm of is_term * is_term * is_type

and argument =
  | Arg_NotAbstract of judgement
  | Arg_Abstract of Name.t * argument

and judgement =
  | JudgementIsType of is_type
  | JudgementIsTerm of is_term
  | JudgementEqType of eq_type
  | JudgementEqTerm of eq_term

and judgement_abstraction = judgement abstraction

and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.t * is_type * 'a abstraction

type boundary =
  | BoundaryIsType of unit
  | BoundaryIsTerm of is_type
  | BoundaryEqType of is_type * is_type
  | BoundaryEqTerm of is_term * is_term * is_type

and boundary_abstraction = boundary abstraction

and premise = boundary_abstraction

type t = Rule of premise list * boundary
