(** The abstract syntax of Andromedan type theory (TT). *)

type bound = int

type ty =
  | TypeConstructor of Name.constructor * argument list
  | TypeMeta of type_meta * term list

and term =
  | TermAtom of atom
  | TermBound of bound
  | TermConstructor of Name.constructor * argument list
  | TermMeta of term_meta * term list
  | TermConvert of term * assumption * ty

and eq_type = EqType of assumption * ty * ty

and eq_term = EqTerm of assumption * term * term * ty

and assumption =
  { free : ty Name.AtomMap.t
  ; is_type_meta : type_boundary Name.MetaMap.t
  ; is_term_meta : term_boundary Name.MetaMap.t
  ; eq_type_meta : eq_type_boundary Name.MetaMap.t
  ; eq_term_meta : eq_term_boundary Name.MetaMap.t
  ; bound : BoundSet.t }

and atom = { atom_name : Name.atom ; atom_type : ty }

and 't meta = { meta_name : Name.meta ; meta_type : 't }

and type_meta = type_boundary meta
and term_meta = term_boundary meta
and eq_type_meta = eq_type_boundary meta
and eq_term_meta = eq_term_boundary meta

and boundary =
    | BoundaryIsType of is_type_boundary
    | BoundaryIsTerm of is_term_boundary
    | BoundaryEqType of eq_type_boundary
    | BoundaryEqTerm of eq_term_boundary

(* Aliases for Jdg *)
and premise_boundary = boundary
and is_type_boundary = type_boundary
and is_term_boundary = term_boundary

and type_boundary = unit abstraction
and term_boundary = ty abstraction
and eq_type_boundary = (ty * ty) abstraction
and eq_term_boundary = (term * term * ty) abstraction

(** An argument of a term or a type constructor *)
and argument =
  | ArgumentIsType of ty abstraction
  | ArgumentIsTerm of term abstraction
  | ArgumentEqType of eq_type abstraction
  | ArgumentEqTerm of eq_term abstraction

(** An abstracted entity. Note that abstractions only ever appear as arguments
   to constructors. Thus we do not carry any type information for the abstracted
   variable, as it can be recovered from the constructor. *)
and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.ident * ty * 'a abstraction


type signature =
  { is_type : Rule.rule_is_type Name.IdentMap.t
  ; is_term : Rule.rule_is_term Name.IdentMap.t
  ; eq_type : Rule.rule_eq_type Name.IdentMap.t
  ; eq_term : Rule.rule_eq_term Name.IdentMap.t
  }

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

  (* ***** JDG **** *)
  | AlphaEqualTypeMismatch of ty * ty
  | AlphaEqualTermMismatch of term * term
  | InvalidConvert of ty * ty

exception Jdg_error of error


type print_env =
  { forbidden : Name.ident list
  ; metas : Name.meta_printer
  ; atoms : Name.atom_printer
  }



(* ******************* JDG ************** *)

type is_term = term

type is_type = ty

type is_atom = atom

type is_type_meta = type_meta
type is_term_meta = term_meta

type is_term_abstraction = is_term abstraction
type is_type_abstraction = is_type abstraction
type eq_type_abstraction = eq_type abstraction
type eq_term_abstraction = eq_term abstraction

type congruence_argument =
  | CongrIsType of is_type abstraction * is_type abstraction * eq_type abstraction
  | CongrIsTerm of is_term abstraction * is_term abstraction * eq_term abstraction
  | CongrEqType of eq_type abstraction * eq_type abstraction
  | CongrEqTerm of eq_term abstraction * eq_term abstraction



(** Stumps are used to construct and invert judgements. The [form_XYZ]
   functions in [Jdg.mli] take a stump and construct a judgement from it,
   whereas the [invert_XYZ] functions do the opposite. We can think of stumps
   as "stumps", i.e., the lowest level of a derivation tree. *)

type nonrec stump_is_type =
  | Stump_TypeConstructor of Name.constructor * argument list
  | Stump_TypeMeta of type_meta * is_term list

and stump_is_term =
  | Stump_TermAtom of is_atom
  | Stump_TermConstructor of Name.constructor * argument list
  | Stump_TermMeta of term_meta * is_term list
  | Stump_TermConvert of is_term * eq_type

and stump_eq_type =
  | Stump_EqType of assumption * is_type * is_type

and stump_eq_term =
  | Stump_EqTerm of assumption * is_term * is_term * is_type

and 'a stump_abstraction =
  | Stump_NotAbstract of 'a
  | Stump_Abstract of is_atom * 'a abstraction
