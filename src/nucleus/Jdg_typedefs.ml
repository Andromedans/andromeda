(** The abstract syntax of Andromedan type theory (TT). *)

module BoundSet = Set.Make (struct
                    type t = int
                    let compare = compare
                  end)

module AtomMap = Name.AtomMap

module MetaMap = Name.MetaMap

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
  { free : ty AtomMap.t
  ; is_type_meta : type_boundary MetaMap.t
  ; is_term_meta : term_boundary MetaMap.t
  ; eq_type_meta : eq_type_boundary MetaMap.t
  ; eq_term_meta : eq_term_boundary MetaMap.t
  ; bound : BoundSet.t }

and atom = { atom_name : Name.atom ; atom_type : ty }

and 't meta = { meta_name : Name.meta ; meta_type : 't }

and type_meta = type_boundary meta
and term_meta = term_boundary meta
and eq_type_meta = eq_type_boundary meta
and eq_term_meta = eq_term_boundary meta

and premise_boundary =
    | BoundaryType of type_boundary
    | BoundaryTerm of term_boundary
    | BoundaryEqType of eq_type_boundary
    | BoundaryEqTerm of eq_term_boundary

and type_boundary = unit abstraction
and term_boundary = ty abstraction
and eq_type_boundary = (ty * ty) abstraction
and eq_term_boundary = (term * term * ty) abstraction

(** An argument of a term or a type constructor *)
and argument =
  | ArgIsType of ty abstraction
  | ArgIsTerm of term abstraction
  | ArgEqType of eq_type abstraction
  | ArgEqTerm of eq_term abstraction

(** An abstracted entity. Note that abstractions only ever appear as arguments
   to constructors. Thus we do not carry any type information for the abstracted
   variable, as it can be recovered from the constructor. *)
and 'a abstraction =
  | NotAbstract of 'a
  | Abstract of Name.ident * ty * 'a abstraction

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

exception Jdg_error of error


type print_env =
  { forbidden : Name.ident list
  ; metas : Name.meta_printer
  ; atoms : Name.atom_printer
  }
