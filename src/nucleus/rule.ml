(** The datatypes for describing the user-definable rules of type theory. *)

(** Meta-variables appearing in rules are referred to by their de Bruijn _indices_. *)
type meta = int

type bound = TT.bound

type ty =
  | TypeConstructor of Name.constructor * argument list
  | TypeMeta of meta * term list

and term =
  | TermBound of bound
  | TermConstructor of Name.constructor * argument list
  | TermMeta of meta * term list

and eq_type = EqType of assumption * ty * ty

and eq_term = EqTerm of assumption * term * term * ty

and argument =
  | ArgIsType of ty abstraction
  | ArgIsTerm of term abstraction
  | ArgEqType of eq_type abstraction
  | ArgEqTerm of eq_term abstraction

and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.ident * ty * 'a abstraction

and assumption = ()

type premise =
  | PremiseIsType of unit abstraction
  | PremiseIsTerm of ty abstraction
  | PremiseEqType of (ty * ty) abstraction
  | PremiseEqTerm of (term * term * ty) abstraction

type rule_is_type = premise list * unit
type rule_is_term = premise list * ty
type rule_eq_type = premise list * (ty * ty)
type rule_eq_term = premise list * (term * term * ty)
