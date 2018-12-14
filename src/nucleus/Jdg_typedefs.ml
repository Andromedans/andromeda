(** The abstract syntax of Andromedan type theory (TT). *)

type bound = int

type is_type =
  | TypeConstructor of Name.constructor * argument list
  | TypeMeta of is_type_meta * is_term list

and is_term =
  | TermAtom of is_atom
  | TermBound of bound
  | TermConstructor of Name.constructor * argument list
  | TermMeta of is_term_meta * is_term list
  | TermConvert of is_term * assumption * is_type

and eq_type = EqType of assumption * is_type * is_type

and eq_term = EqTerm of assumption * is_term * is_term * is_type

and is_atom = { atom_name : Name.atom ; atom_type : is_type }

and 't meta = { meta_name : Name.meta ; meta_type : 't }

and is_type_meta = is_type_boundary meta
and is_term_meta = is_term_boundary meta
and eq_type_meta = eq_type_boundary meta
and eq_term_meta = eq_term_boundary meta

and assumption =
  { free : is_type Name.AtomMap.t
  ; is_type_meta : is_type_boundary Name.MetaMap.t
  ; is_term_meta : is_term_boundary Name.MetaMap.t
  ; eq_type_meta : eq_type_boundary Name.MetaMap.t
  ; eq_term_meta : eq_term_boundary Name.MetaMap.t
  ; bound : BoundSet.t }

and is_type_boundary = unit abstraction
and is_term_boundary = is_type abstraction
and eq_type_boundary = (is_type * is_type) abstraction
and eq_term_boundary = (is_term * is_term * is_type) abstraction

and boundary =
    | BoundaryIsType of is_type_boundary
    | BoundaryIsTerm of is_term_boundary
    | BoundaryEqType of eq_type_boundary
    | BoundaryEqTerm of eq_term_boundary

and argument =
  | ArgumentIsType of is_type abstraction
  | ArgumentIsTerm of is_term abstraction
  | ArgumentEqType of eq_type abstraction
  | ArgumentEqTerm of eq_term abstraction

and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.ident * is_type * 'a abstraction


type signature =
  { is_type : Rule.rule_is_type Name.IdentMap.t
  ; is_term : Rule.rule_is_term Name.IdentMap.t
  ; eq_type : Rule.rule_eq_type Name.IdentMap.t
  ; eq_term : Rule.rule_eq_term Name.IdentMap.t
  }

type is_term_abstraction = is_term abstraction
type is_type_abstraction = is_type abstraction
type eq_type_abstraction = eq_type abstraction
type eq_term_abstraction = eq_term abstraction

(** Stumps are used to construct and invert judgements. The [form_XYZ]
   functions in [Jdg.mli] take a stump and construct a judgement from it,
   whereas the [invert_XYZ] functions do the opposite. We can think of stumps
   as "stumps", i.e., the lowest level of a derivation tree. *)

type nonrec stump_is_type =
  | Stump_TypeConstructor of Name.constructor * argument list
  | Stump_TypeMeta of is_type_meta * is_term list

and stump_is_term =
  | Stump_TermAtom of is_atom
  | Stump_TermConstructor of Name.constructor * argument list
  | Stump_TermMeta of is_term_meta * is_term list
  | Stump_TermConvert of is_term * eq_type

and stump_eq_type =
  | Stump_EqType of assumption * is_type * is_type

and stump_eq_term =
  | Stump_EqTerm of assumption * is_term * is_term * is_type

and 'a stump_abstraction =
  | Stump_NotAbstract of 'a
  | Stump_Abstract of is_atom * 'a abstraction

type congruence_argument =
  | CongrIsType of is_type abstraction * is_type abstraction * eq_type abstraction
  | CongrIsTerm of is_term abstraction * is_term abstraction * eq_term abstraction
  | CongrEqType of eq_type abstraction * eq_type abstraction
  | CongrEqTerm of eq_term abstraction * eq_term abstraction

(* Sometimes we work with meta-variables in their _de Bruijn index_ order, i.e.,
   as a list whose first element is de Bruijn index 0, and sometimes we work in
   the _constructor_ order, i.e., in the order of premises to a rule. These
   are reverse from each other. We have found it to be quite error-prone to
   keep track of which order any given list might be, so we use some abstract
   types to reduce the possibility of further bugs.

   Used by module Indices
*)
type indices = argument list

type error =
  | InvalidInstantiation
  | InvalidAbstraction
  | TooFewArguments
  | TooManyArguments
  | TermExpected
  | TypeExpected
  | ExtraAssumptions
  | InvalidApplication
  | InvalidArgument
  | IsTypeExpected
  | IsTermExpected
  | EqTypeExpected
  | EqTermExpected
  | AbstractionExpected
  | InvalidSubstitution
  | InvalidCongruence
  | AlphaEqualTypeMismatch of is_type * is_type
  | AlphaEqualTermMismatch of is_term * is_term
  | InvalidConvert of is_type * is_type

exception Jdg_error of error

type print_env =
  { forbidden : Name.ident list
  ; metas : Name.meta_printer
  ; atoms : Name.atom_printer
  }
