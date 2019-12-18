(** Printing environment *)
type print_environment = {
  forbidden : Name.set ;
  debruijn_var : Name.t list ;
  debruijn_meta : Name.t list ;
  opens : Path.set
}

(** The description of a user-defined type theory *)
type signature

(** The datatypes for judgements are abstract. Their deconstruction is
   controlled through the various inversion functions which make sure that the
   user cannot get their hands on an invalid judgement (in particular, one that
   has a freely handing bound variable. *)

(** Judgements can be abstracted *)
type 'a abstraction

(** Judgement that something is a term. *)
type is_term

(** Judgement that something is an atom. *)
type is_atom

(** Judgement that something is a type. *)
type is_type

(** Judgement that something is a type equality. *)
type eq_type

(** Judgement that something is a term equality. *)
type eq_term

(** Shorthands for abstracted judgements. *)
type is_term_abstraction = is_term abstraction
type is_type_abstraction = is_type abstraction
type eq_type_abstraction = eq_type abstraction
type eq_term_abstraction = eq_term abstraction

(** Judgement *)
type judgement =
  | JudgementIsType of is_type
  | JudgementIsTerm of is_term
  | JudgementEqType of eq_type
  | JudgementEqTerm of eq_term

(** A shorthand abstracted judgement *)
type judgement_abstraction = judgement abstraction

(** Boundary of a type judgement, it is safe to expose it since the user cannot create an
   invalid unit. *)
type is_type_boundary = unit

(** Boundary of a term judgement, it is safe to expose it since the user cannot create an
   invalid type judgement. *)
type is_term_boundary = is_type

(** Boundary of a type equality judgement, it is safe to expose it since the user cannot create an
   invalid type judgements. *)
type eq_type_boundary = is_type * is_type

(** Boundary of a term equality judgement. It is *not* safe to expose it since a term boundary
    consists of terms [e1] and [e2] which both have type [t]. If we exposed the type, the user
    could create an invalid boundary in which the types of [e1] and [e2] do not match. *)
type eq_term_boundary

(** Boundary of a judgement *)
type boundary =
  | BoundaryIsType of is_type_boundary
  | BoundaryIsTerm of is_term_boundary
  | BoundaryEqType of eq_type_boundary
  | BoundaryEqTerm of eq_term_boundary

(** A shorthand for abstracted boundary *)
type boundary_abstraction = boundary abstraction

type assumption

type meta

(** A stump is obtained when we invert a judgement. *)

type nonrec stump_is_type =
  | Stump_TypeConstructor of Ident.t * judgement_abstraction list
  | Stump_TypeMeta of meta * is_term list

and stump_is_term =
  | Stump_TermAtom of is_atom
  | Stump_TermConstructor of Ident.t * judgement_abstraction list
  | Stump_TermMeta of meta * is_term list
  | Stump_TermConvert of is_term * eq_type

and stump_eq_type =
  | Stump_EqType of assumption * is_type * is_type

and stump_eq_term =
  | Stump_EqTerm of assumption * is_term * is_term * is_type

and 'a stump_abstraction =
  | Stump_NotAbstract of 'a
  | Stump_Abstract of is_atom * 'a abstraction

(** An inference rule *)
type 'a rule

type primitive = boundary rule

type derivation = judgement rule

(** Type theory signature. *)
module Signature : sig

  val empty : signature

  val add_rule : Ident.t -> primitive -> signature -> signature
end

(** Form a primitive rule from a given list of meta-variables and a boundary *)
val form_rule : meta list -> boundary -> primitive

(** Form a derived rule from a given list of meta-variables and a boundary *)
val form_derivation : meta list -> judgement -> derivation

(** Functions that expose abstract types. These are harmless because there is no way
    to map back into the absract types. *)
val expose_is_term : is_term -> Nucleus_types.is_term
val expose_is_type : is_type -> Nucleus_types.is_type
val expose_eq_type : eq_type -> Nucleus_types.eq_type
val expose_eq_term : eq_term -> Nucleus_types.eq_term
val expose_judgement : judgement -> Nucleus_types.judgement
val expose_rule : 'a rule -> 'a Nucleus_types.rule

(** When we apply a rule application to one more argument two things may happen.
   Either we are done and we get a result, or more arguments are needed, in
   which case we get the rap with one more argument applied, and the boundary of
   the next argument. *)
type 'a rule_application = private
  | RapDone of 'a
  | RapMore of boundary_abstraction * (judgement_abstraction -> 'a rule_application)

(** Form a fully non-applied rule application for a given constructor *)
val form_constructor_rap : signature -> Ident.t -> judgement rule_application

(** Form a fully non-applied meta-variable application for a given meta-variable *)
val form_meta_rap : signature -> meta -> judgement rule_application

(** Form a fully non-applied rule application with a type conclusion *)
val form_is_type_rap : signature -> is_type rule -> is_type rule_application

(** Form a fully non-applied rule application with a term conclusion *)
val form_is_term_rap : signature -> is_term rule -> is_term rule_application

(** Form a fully non-applied rule application with a type equality conclusion *)
val form_eq_type_rap : signature -> eq_type rule -> eq_type rule_application

(** Form a fully non-applied rule application with a term equality conclusion *)
val form_eq_term_rap : signature -> eq_term rule -> eq_term rule_application

(** Form a fully non-applied derivation application *)
val form_derivation_rap : signature -> derivation -> judgement rule_application

(** Convert atom judgement to term judgement *)
val form_is_term_atom : is_atom -> is_term

(** [form_meta x abstr] creates an eta-expanded fresh meta-variable with the given
   boundary abstraction for an object boundary. For an equality boundary it creates an
   abstracted equality judgement. It returns the meta-variable that it created, and the
   created judgement. For equality judgements, it returns a dummy meta that does not
   appear anywhere. *)
val form_meta : Name.t -> boundary_abstraction -> meta * judgement_abstraction

val meta_nonce : meta -> Nonce.t
val meta_boundary : meta -> boundary_abstraction

(** Convert the given term along the given equality type. *)
val form_is_term_convert : signature -> is_term -> eq_type -> is_term

(** Form a boundary *)
val form_is_type_boundary : boundary
val form_is_term_boundary : is_type -> boundary
val form_eq_type_boundary : is_type -> is_type -> boundary
val form_eq_term_boundary : signature -> is_term -> is_term -> boundary
val form_is_term_boundary_abstraction : is_type_abstraction -> boundary_abstraction

(** Form a non-abstracted abstraction *)
val abstract_not_abstract : 'a -> 'a abstraction

(** Abstract an abstraction by one more level. *)
val abstract_is_type : ?name:Name.t -> is_atom -> is_type_abstraction -> is_type_abstraction
val abstract_is_term : ?name:Name.t -> is_atom -> is_term_abstraction -> is_term_abstraction
val abstract_eq_type : ?name:Name.t -> is_atom -> eq_type_abstraction -> eq_type_abstraction
val abstract_eq_term : ?name:Name.t -> is_atom -> eq_term_abstraction -> eq_term_abstraction

(** Abstract a judgement abstraction by one more level *)
val abstract_judgement : ?name:Name.t -> is_atom -> judgement_abstraction -> judgement_abstraction

(** Abstract a boundary abstraction *)
val abstract_boundary : is_atom -> boundary_abstraction -> boundary_abstraction

(** [fresh_atom x t] Create a fresh atom from name [x] with type [t] *)
val fresh_atom : Name.t -> is_type -> is_atom

(** Verify that an abstraction is in fact not abstract. *)
val as_not_abstract : 'a abstraction -> 'a option

(** Various coercion functions between general and specific forms *)

val as_is_type_abstraction : judgement_abstraction -> is_type abstraction option
val as_is_term_abstraction : judgement_abstraction -> is_term abstraction option
val as_eq_type_abstraction : judgement_abstraction -> eq_type abstraction option
val as_eq_term_abstraction : judgement_abstraction -> eq_term abstraction option

val as_is_type : judgement -> is_type option
val as_is_term : judgement -> is_term option
val as_eq_type : judgement -> eq_type option
val as_eq_term : judgement -> eq_term option

val from_is_type_abstraction : is_type_abstraction -> judgement_abstraction
val from_is_term_abstraction : is_term_abstraction -> judgement_abstraction
val from_eq_type_abstraction : eq_type_abstraction -> judgement_abstraction
val from_eq_term_abstraction : eq_term_abstraction -> judgement_abstraction

val as_is_type_boundary_abstraction : boundary_abstraction -> is_type_boundary abstraction option
val as_is_term_boundary_abstraction : boundary_abstraction -> is_term_boundary abstraction option
val as_eq_type_boundary_abstraction : boundary_abstraction -> eq_type_boundary abstraction option
val as_eq_term_boundary_abstraction : boundary_abstraction -> eq_term_boundary abstraction option

val as_is_type_boundary : boundary -> is_type_boundary option
val as_is_term_boundary : boundary -> is_term_boundary option
val as_eq_type_boundary : boundary -> eq_type_boundary option
val as_eq_term_boundary : boundary -> eq_term_boundary option

val from_is_type_boundary_abstraction : is_type_boundary abstraction -> boundary_abstraction
val from_is_term_boundary_abstraction : is_term_boundary abstraction -> boundary_abstraction
val from_eq_type_boundary_abstraction : eq_type_boundary abstraction -> boundary_abstraction
val from_eq_term_boundary_abstraction : eq_term_boundary abstraction -> boundary_abstraction

(** Convert the conclusion of a rule from a judgement to a type, if possible. *)
val as_is_type_rule : derivation -> is_type rule option

(** Convert the conclusion of a rule from a judgement to a term, if possible. *)
val as_is_term_rule : derivation -> is_term rule option

(** Convert the conclusion of a rule from a judgement to a type equation, if possible. *)
val as_eq_type_rule : derivation -> eq_type rule option

(** Convert the conclusion of a rule from a judgement to a term equation, if possible. *)
val as_eq_term_rule : derivation -> eq_term rule option

(** Conversions *)
val convert_term : signature -> is_term -> eq_type -> is_term option
val convert_term_abstraction : signature -> is_term abstraction -> eq_type abstraction -> is_term abstraction option
val convert_eq_term : eq_term -> eq_type -> eq_term option
val convert_eq_term_abstraction : eq_term abstraction -> eq_type abstraction -> eq_term abstraction option
val convert_judgement_abstraction : signature -> judgement_abstraction -> eq_type_abstraction -> judgement_abstraction option

(** Inversion principles *)

val invert_is_type : signature -> is_type -> stump_is_type

val invert_is_term : signature -> is_term -> stump_is_term

val invert_eq_type : eq_type -> stump_eq_type

(** Invert a term equality [e1 == e2 : t] to give [e1], [e2] and [t].
    We guarantee that [e1 : t] and [e2 : t], i.e., if necessary [e1]
    and [e2] are converted to have type [t]. *)
val invert_eq_term : signature -> eq_term -> stump_eq_term

val atom_nonce : is_atom -> Nonce.t

val atom_name : is_atom -> Name.t

val invert_is_term_abstraction :
  ?name:Name.t -> is_term_abstraction -> is_term stump_abstraction

val invert_is_type_abstraction :
  ?name:Name.t -> is_type_abstraction -> is_type stump_abstraction

val invert_eq_type_abstraction :
  ?name:Name.t -> eq_type_abstraction -> eq_type stump_abstraction

val invert_eq_term_abstraction :
  ?name:Name.t -> eq_term_abstraction -> eq_term stump_abstraction

val invert_judgement_abstraction :
  ?name:Name.t -> judgement_abstraction -> judgement stump_abstraction

val invert_eq_term_boundary :
  eq_term_boundary -> is_term * is_term * is_type

val invert_is_term_boundary_abstraction :
  ?name:Name.t -> is_term_boundary abstraction -> is_type stump_abstraction

val invert_is_type_boundary_abstraction :
  ?name:Name.t -> is_type_boundary abstraction -> unit stump_abstraction

val invert_eq_type_boundary_abstraction :
  ?name:Name.t -> eq_type_boundary abstraction -> (is_type * is_type) stump_abstraction

val invert_eq_term_boundary_abstraction :
  ?name:Name.t -> eq_term_boundary abstraction -> eq_term_boundary stump_abstraction

val invert_boundary_abstraction :
  ?name:Name.t -> boundary_abstraction -> boundary stump_abstraction

val context_is_type_abstraction : is_type_abstraction -> is_atom list
val context_is_term_abstraction : is_term_abstraction -> is_atom list
val context_eq_type_abstraction : eq_type_abstraction -> is_atom list
val context_eq_term_abstraction : eq_term_abstraction -> is_atom list

(** The type judgement of a term judgement. *)
val type_of_term : signature -> is_term -> is_type

(** The abstracted type judgement of an abstracted term judgement. *)
val type_of_term_abstraction : signature -> is_term_abstraction -> is_type_abstraction

(** The type over which an abstraction is abstracting, or [None] if it not an
   abstraction. *)
val type_at_abstraction : 'a abstraction -> is_type option

(** Checking that an abstracted judgement has the desired boundary *)
val check_judgement_boundary_abstraction : signature -> judgement_abstraction -> boundary_abstraction -> bool

(** Typeof for atoms *)
val type_of_atom : is_atom -> is_type

(** Does this atom occur in this judgement? *)
val occurs_is_type_abstraction : is_atom -> is_type_abstraction -> bool
val occurs_is_term_abstraction : is_atom -> is_term_abstraction -> bool
val occurs_eq_type_abstraction : is_atom -> eq_type_abstraction -> bool
val occurs_eq_term_abstraction : is_atom -> eq_term_abstraction -> bool
val occurs_judgement_abstraction : is_atom -> judgement_abstraction -> bool

val apply_is_type_abstraction :
  signature -> is_type_abstraction -> is_term -> is_type_abstraction

val apply_is_term_abstraction :
  signature -> is_term_abstraction -> is_term -> is_term_abstraction

val apply_eq_type_abstraction :
  signature -> eq_type_abstraction -> is_term -> eq_type_abstraction

val apply_eq_term_abstraction :
  signature -> eq_term_abstraction -> is_term -> eq_term_abstraction

val apply_judgement_abstraction :
  signature -> judgement_abstraction -> is_term -> judgement_abstraction

val apply_is_type_boundary_abstraction :
  signature -> is_type_boundary abstraction -> is_term -> is_type_boundary abstraction

val apply_is_term_boundary_abstraction :
  signature -> is_term_boundary abstraction -> is_term -> is_term_boundary abstraction

val apply_eq_type_boundary_abstraction :
  signature -> eq_type_boundary abstraction -> is_term -> eq_type_boundary abstraction

val apply_eq_term_boundary_abstraction :
  signature -> eq_term_boundary abstraction -> is_term -> eq_term_boundary abstraction

val apply_boundary_abstraction :
  signature -> boundary_abstraction -> is_term -> boundary_abstraction


(** If [e1 == e2 : A] and [A == B] then [e1 == e2 : B] *)
val form_eq_term_convert : eq_term -> eq_type -> eq_term

(** Given two terms [e1 : A1] and [e2 : A2] construct [e1 == e2 : A1],
    provided [A1] and [A2] are alpha equal and [e1] and [e2] are alpha equal *)
val form_alpha_equal_term : signature -> is_term -> is_term -> eq_term option

(** Given two types [A] and [B] construct [A == B] provided the types are alpha equal *)
val form_alpha_equal_type : is_type -> is_type -> eq_type option

(** Given two abstractions, construct an abstracted equality provided the abstracted entities are alpha equal. *)
val form_alpha_equal_abstraction :
  ('a -> 'b -> 'c option) ->
  'a abstraction -> 'b abstraction -> 'c abstraction option

(** Test whether terms are alpha-equal. They may have different types and incompatible contexts even if [true] is returned. *)
val alpha_equal_term : is_term -> is_term -> bool

(** Test whether types are alpha-equal. They may have different contexts. *)
val alpha_equal_type : is_type -> is_type -> bool

(** Test whether atoms are alpha-equal. *)
val alpha_equal_atom : is_atom -> is_atom -> bool

(** Test whether two abstractions are alpha-equal. *)
val alpha_equal_abstraction : ('a -> 'a -> bool) -> 'a abstraction -> 'a abstraction -> bool

(** Test whether two judgements are alpha-equal. *)
val alpha_equal_judgement : judgement -> judgement -> bool

(** Test whether two boundaries are alpha-equal. *)
val alpha_equal_boundary : boundary -> boundary -> bool

(** Witness reflexivity of a type. *)
val reflexivity_type : is_type -> eq_type

(** Witness reflexivity of a term. *)
val reflexivity_term : signature -> is_term -> eq_term

(** Witness reflexivity of an abstracted object judgement, return [None] if given an equality judgement. *)
val reflexivity_judgement_abstraction : signature -> judgement_abstraction -> judgement_abstraction option

(** If [e1 == e2 : A] then [e2 == e1 : A] *)
val symmetry_term : eq_term -> eq_term

(** If [A == B] then [B == A] *)
val symmetry_type : eq_type -> eq_type

(** If [e1 == e2 : A] and [e2 == e3 : B] then [e1 == e2 : A]. The rule is valid by
   uniqueness of typing: [e2] has both type [A] and [B]. *)
val transitivity_term : eq_term -> eq_term -> eq_term

(** If [e1 == e2 : A] and [e2 == e3 : B] then [e1 == e2 : B]. The rule is valid by
   uniqueness of typing: [e2] has both type [A] and [B]. *)
val transitivity_term' : eq_term -> eq_term -> eq_term

(** If [A == B] and [B == C] then [A == C] *)
val transitivity_type : eq_type -> eq_type -> eq_type

(** Given [e : A], compute the natural type of [e] as [B], return [B == A] *)
val natural_type_eq : signature -> is_term -> eq_type

(** Congruence rules *)

(** Create the congruence rule application for the given constructor and
    judgements, or raise [InvalidCongruence] if the judgements are not
    of the correct form. *)
val congruence_judgement :
  signature -> judgement -> judgement -> judgement rule_application

val congruence_is_type :
  signature -> is_type -> is_type -> eq_type rule_application option

val congruence_is_term :
  signature -> is_term -> is_term -> eq_term rule_application option

(** Give human names to things *)

val name_of_judgement : judgement_abstraction -> string
val name_of_boundary : boundary_abstraction -> string

(** Printing routines *)

val print_is_term :
  ?max_level:Level.t -> penv:print_environment -> is_term -> Format.formatter -> unit

val print_is_type :
  ?max_level:Level.t -> penv:print_environment -> is_type -> Format.formatter -> unit

val print_eq_term :
  ?max_level:Level.t -> penv:print_environment -> eq_term -> Format.formatter -> unit

val print_eq_type :
  ?max_level:Level.t -> penv:print_environment -> eq_type -> Format.formatter -> unit

val print_is_term_abstraction :
  ?max_level:Level.t -> penv:print_environment -> is_term_abstraction -> Format.formatter -> unit

val print_is_type_abstraction :
  ?max_level:Level.t -> penv:print_environment -> is_type_abstraction -> Format.formatter -> unit

val print_eq_term_abstraction :
  ?max_level:Level.t -> penv:print_environment -> eq_term_abstraction -> Format.formatter -> unit

val print_eq_type_abstraction :
  ?max_level:Level.t -> penv:print_environment -> eq_type_abstraction -> Format.formatter -> unit

val print_judgement_abstraction :
  ?max_level:Level.t -> penv:print_environment -> judgement_abstraction -> Format.formatter -> unit

val print_boundary_abstraction :
  ?max_level:Level.t -> penv:print_environment -> boundary_abstraction -> Format.formatter -> unit

val print_derivation :
  ?max_level:Level.t -> penv:print_environment -> derivation -> Format.formatter -> unit


(** An error emitted by the nucleus *)
type error

exception Error of error

(** Print a nucleus error *)
val print_error : penv:print_environment -> error -> Format.formatter -> unit

module Json :
sig
  val judgement_abstraction : judgement_abstraction -> Json.t

  val boundary_abstraction : boundary_abstraction -> Json.t
end
