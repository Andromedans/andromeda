(** The datatypes for describing the user-definable rules of type theory. *)

(** Meta-variables appearing in rules are referred to by their de Bruijn _indices_. *)
type meta = int

type bound = int

type ty =
  | TypeConstructor of Ident.t * argument_abstraction list
  | TypeMeta of meta * term list

and term =
  | TermBound of bound
  | TermConstructor of Ident.t * argument_abstraction list
  | TermMeta of meta * term list

and eq_type = EqType of ty * ty

and eq_term = EqTerm of term * term * ty

and argument =
  | JudgementIsType of ty
  | JudgementIsTerm of term
  | JudgementEqType of eq_type
  | JudgementEqTerm of eq_term

and argument_abstraction = argument abstraction

and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.t * ty * 'a abstraction

type premise =
  | PremiseIsType of unit
  | PremiseIsTerm of ty
  | PremiseEqType of ty * ty
  | PremiseEqTerm of term * term * ty

and premise_abstraction = premise abstraction

type rule_is_type = premise_abstraction list * unit
type rule_is_term = premise_abstraction list * ty
type rule_eq_type = premise_abstraction list * (ty * ty)
type rule_eq_term = premise_abstraction list * (term * term * ty)
