(** The datatypes for describing the user-definable rules of type theory. *)

type meta = int  (* meta-variables appearing in rules *)
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
  | PremiseIsType of Name.ident * unit abstraction
  | PremiseIsTerm of Name.ident * ty abstraction
  | PremiseEqType of (ty * ty) abstraction
  | PremiseEqTerm of (term * term * ty) abstraction

type is_type_rule = premise list
type is_term_rule = premise list * ty
type eq_type_rule = premise list * (ty * ty)
type eq_term_rule = premise list * (term * term * ty)
