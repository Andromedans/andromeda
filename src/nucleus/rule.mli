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
  | ArgumentIsType of ty abstraction
  | ArgumentIsTerm of term abstraction
  | ArgumentEqType of eq_type abstraction
  | ArgumentEqTerm of eq_term abstraction

and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.t * ty * 'a abstraction

type premise =
  | PremiseIsType of unit abstraction
  | PremiseIsTerm of ty abstraction
  | PremiseEqType of (ty * ty) abstraction
  | PremiseEqTerm of (term * term * ty) abstraction

type rule_is_type = premise list * unit
type rule_is_term = premise list * ty
type rule_eq_type = premise list * (ty * ty)
type rule_eq_term = premise list * (term * term * ty)
