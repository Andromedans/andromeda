(** The datatypes for describing the user-definable rules of type theory. *)

(** Meta-variables appearing in rules are referred to by their de Bruijn _indices_. *)
type meta = int

type bound = int

type ty =
  | TypeConstructor of Ident.t * argument list
  | TypeMeta of meta * term list

and term =
  | TermBound of bound
  | TermConstructor of Ident.t * argument list
  | TermMeta of meta * term list

and eq_type = EqType of ty * ty

and eq_term = EqTerm of term * term * ty

and argument =
  | Arg_NotAbstract of judgement
  | Arg_Abstract of Name.t * argument

and judgement =
  | JudgementIsType of ty
  | JudgementIsTerm of term
  | JudgementEqType of eq_type
  | JudgementEqTerm of eq_term

and judgement_abstraction = judgement abstraction

and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.t * ty * 'a abstraction

type boundary =
  | BoundaryIsType of unit
  | BoundaryIsTerm of ty
  | BoundaryEqType of ty * ty
  | BoundaryEqTerm of term * term * ty

and boundary_abstraction = boundary abstraction

and premise = boundary_abstraction

type t = Rule of premise list * boundary
