(** Printing environment *)
type print_environment = {
  forbidden : Name.set ;
  debruijn : Name.t list ;
  opens : Path.set
}

(** The description of a user-defined type theory *)
type signature

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


(** An argument to a term or type constructor *)
type argument =
  | ArgumentIsType of is_type_abstraction
  | ArgumentIsTerm of is_term_abstraction
  | ArgumentEqType of eq_type_abstraction
  | ArgumentEqTerm of eq_term_abstraction

(** Boundary of a type judgement *)
type is_type_boundary = unit abstraction

(** Boundary of a term judgement *)
type is_term_boundary = is_type abstraction

(** Boundary of a type equality judgement *)
type eq_type_boundary = (is_type * is_type) abstraction

(** Boundary of a term equality judgement *)
type eq_term_boundary = (is_term * is_term * is_type) abstraction

(** Boundary of a judgement *)
type boundary =
    | BoundaryIsType of is_type_boundary
    | BoundaryIsTerm of is_term_boundary
    | BoundaryEqType of eq_type_boundary
    | BoundaryEqTerm of eq_term_boundary

type assumption

type 'a meta
type is_type_meta = is_type_boundary meta
type is_term_meta = is_term_boundary meta
type eq_type_meta = eq_type_boundary meta
type eq_term_meta = eq_term_boundary meta

(** A stump is obtained when we invert a judgement. *)

type nonrec stump_is_type =
  | Stump_TypeConstructor of Ident.t * argument list
  | Stump_TypeMeta of is_type_meta * is_term list

and stump_is_term =
  | Stump_TermAtom of is_atom
  | Stump_TermConstructor of Ident.t * argument list
  | Stump_TermMeta of is_term_meta * is_term list
  | Stump_TermConvert of is_term * eq_type

and stump_eq_type =
  | Stump_EqType of assumption * is_type * is_type

and stump_eq_term =
  | Stump_EqTerm of assumption * is_term * is_term * is_type

and 'a stump_abstraction =
  | Stump_NotAbstract of 'a
  | Stump_Abstract of is_atom * 'a abstraction


(** An auxiliary type for providing arguments to a congruence rule. Each arguments is like
   two endpoints with a path between them, except that no paths between equalities are
   needed. *)
type congruence_argument =
  | CongrIsType of is_type_abstraction * is_type_abstraction * eq_type_abstraction
  | CongrIsTerm of is_term_abstraction * is_term_abstraction * eq_term_abstraction
  | CongrEqType of eq_type_abstraction * eq_type_abstraction
  | CongrEqTerm of eq_term_abstraction * eq_term_abstraction

module Signature : sig

  val empty : signature

  val add_rule_is_type : Ident.t -> Rule.rule_is_type -> signature -> signature
  val add_rule_is_term : Ident.t -> Rule.rule_is_term -> signature -> signature
  val add_rule_eq_type : Ident.t -> Rule.rule_eq_type -> signature -> signature
  val add_rule_eq_term : Ident.t -> Rule.rule_eq_term -> signature -> signature

end

val form_rule_is_type :
  (Nonce.t * boundary) list -> Rule.rule_is_type

val form_rule_is_term :
  (Nonce.t * boundary) list -> is_type -> Rule.rule_is_term

val form_rule_eq_type :
  (Nonce.t * boundary) list -> is_type * is_type -> Rule.rule_eq_type

val form_rule_eq_term :
  (Nonce.t * boundary) list -> is_term * is_term * is_type -> Rule.rule_eq_term

(** A partially applied rule is a rule with an initial part of the premises
   applied already. We need to represent such partial applications in order to
   be able to compute the boundary of the next argument from the already given
   ones _before_ the next argument is known. We call such a partially applied
   rule a (partial) _rule application_. *)
type 'a rule_application_status

(** When we apply a rule application to one more argument two things may happen.
   Either we are done and we get a result, or more arguments are needed, in
   which case we get the rap with one more argument applied, and the boundary of
   the next argument. *)
type 'a rule_application = private
  | RapDone of 'a
  | RapMore of 'a rule_application_status

(** Form a fully non-applied rule application for a given constructor *)
val form_rap_is_type : signature -> Ident.t -> is_type rule_application
val form_rap_is_term : signature -> Ident.t -> is_term rule_application
val form_rap_eq_type : signature -> Ident.t -> eq_type rule_application
val form_rap_eq_term : signature -> Ident.t -> eq_term rule_application

(** Apply a rap to one more argument *)
val rap_apply : signature -> 'a rule_application_status -> argument -> 'a rule_application

(** Give the boundary of a rap status, i.e., the boundary of the next argument. *)
val rap_boundary : 'a rule_application_status -> boundary

(** Convert atom judgement to term judgement *)
val form_is_term_atom : is_atom -> is_term

(** [form_is_type_meta sgn a args] creates a is_type judgement by applying the
    meta-variable [a] = `x : A, ..., y : B ⊢ jdg` to a list of terms [args] of
    matching types. *)
val form_is_type_meta : signature -> is_type_meta -> is_term list -> is_type

(** [form_is_term_meta sgn a args] creates a is_term judgement by applying the
    meta-variable [a] = `x : A, ..., y : B ⊢ jdg` to a list of terms [args] of
    matching types. *)
val form_is_term_meta : signature -> is_term_meta -> is_term list -> is_term

val form_is_term_convert : signature -> is_term -> eq_type -> is_term

val form_eq_type_meta : signature -> eq_type_meta -> is_term list -> eq_type

val form_eq_term_meta : signature -> eq_term_meta -> is_term list -> eq_term

(** Form a non-abstracted abstraction *)
val abstract_not_abstract : 'a -> 'a abstraction

(** Form an abstracted judgement *)
val abstract_is_type : is_atom -> is_type_abstraction -> is_type_abstraction
val abstract_is_term : is_atom -> is_term_abstraction -> is_term_abstraction
val abstract_eq_type : is_atom -> eq_type_abstraction -> eq_type_abstraction
val abstract_eq_term : is_atom -> eq_term_abstraction -> eq_term_abstraction

(** Form an abstracted boundary *)
val abstract_boundary_is_type : is_atom -> is_type_boundary -> is_type_boundary
val abstract_boundary_is_term : is_atom -> is_term_boundary -> is_term_boundary
val abstract_boundary_eq_type : is_atom -> eq_type_boundary -> eq_type_boundary
val abstract_boundary_eq_term : is_atom -> eq_term_boundary -> eq_term_boundary

(** [fresh_atom x t] Create a fresh atom from name [x] with type [t] *)
val fresh_atom : Name.t -> is_type -> is_atom

(** [fresh_is_type_meta x abstr] creates a fresh type meta-variable of type [abstr] *)
val fresh_is_type_meta : Name.t -> is_type_boundary -> is_type_meta
val fresh_is_term_meta : Name.t -> is_term_boundary -> is_term_meta
val fresh_eq_type_meta : Name.t -> eq_type_boundary -> eq_type_meta
val fresh_eq_term_meta : Name.t -> eq_term_boundary -> eq_term_meta

val is_type_meta_eta_expanded : signature -> is_type_meta -> is_type_abstraction
val is_term_meta_eta_expanded : signature -> is_term_meta -> is_term_abstraction
val eq_type_meta_eta_expanded : signature -> eq_type_meta -> eq_type_abstraction
val eq_term_meta_eta_expanded : signature -> eq_term_meta -> eq_term_abstraction

(** Verify that an abstraction is in fact not abstract *)
val as_not_abstract : 'a abstraction -> 'a option

(** Inversion principles *)

val invert_is_type : is_type -> stump_is_type

val invert_is_term : signature -> is_term -> stump_is_term

val invert_eq_type : eq_type -> stump_eq_type

val atom_name : is_atom -> Name.t

val meta_nonce : 'a meta -> Nonce.t

val invert_is_term_abstraction :
  ?name:Name.t -> is_term_abstraction -> is_term stump_abstraction

val invert_is_type_abstraction :
  ?name:Name.t -> is_type_abstraction -> is_type stump_abstraction

val invert_eq_type_abstraction :
  ?name:Name.t -> eq_type_abstraction -> eq_type stump_abstraction

val invert_eq_term_abstraction :
  ?name:Name.t -> eq_term_abstraction -> eq_term stump_abstraction

val invert_is_term_boundary :
  ?name:Name.t -> is_term_boundary -> is_term stump_abstraction

val invert_is_type_boundary :
  ?name:Name.t -> is_type_boundary -> is_type stump_abstraction

val invert_eq_type_boundary :
  ?name:Name.t -> eq_type_boundary -> eq_type stump_abstraction

val invert_eq_term_boundary :
  ?name:Name.t -> eq_term_boundary -> eq_term stump_abstraction

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
val check_is_type_boundary : is_type_abstraction -> is_type_boundary -> bool
val check_is_term_boundary : signature -> is_term_abstraction -> is_term_boundary -> bool
val check_eq_type_boundary : eq_type_abstraction -> eq_type_boundary -> bool
val check_eq_term_boundary : eq_term_abstraction -> eq_term_boundary -> bool

(** Typeof for atoms *)
val type_of_atom : is_atom -> is_type

(** Does this atom occur in this judgement? *)
val occurs_is_type_abstraction : is_atom -> is_type_abstraction -> bool
val occurs_is_term_abstraction : is_atom -> is_term_abstraction -> bool
val occurs_eq_type_abstraction : is_atom -> eq_type_abstraction -> bool
val occurs_eq_term_abstraction : is_atom -> eq_term_abstraction -> bool

val apply_is_type_abstraction :
  signature -> is_type_abstraction -> is_term -> is_type_abstraction

val apply_is_term_abstraction :
  signature -> is_term_abstraction -> is_term -> is_term_abstraction

val apply_eq_type_abstraction :
  signature -> eq_type_abstraction -> is_term -> eq_type_abstraction

val apply_eq_term_abstraction :
  signature -> eq_term_abstraction -> is_term -> eq_term_abstraction

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

(** Test whether two abstractions are alpha-equal. *)
val alpha_equal_abstraction
  : ('a -> 'a -> bool) -> 'a abstraction -> 'a abstraction -> bool

(** If [e1 == e2 : A] then [e2 == e1 : A] *)
val symmetry_term : eq_term -> eq_term

(** If [A == B] then [B == A] *)
val symmetry_type : eq_type -> eq_type

(** If [e1 == e2 : A] and [e2 == e3 : A] then [e1 == e2 : A] *)
val transitivity_term : eq_term -> eq_term -> eq_term

(** If [A == B] and [B == C] then [A == C] *)
val transitivity_type : eq_type -> eq_type -> eq_type

(** Given [e : A], compute the natural type of [e] as [B], return [B == A] *)
val natural_type_eq : signature -> is_term -> eq_type

(** Congruence rules *)

val congruence_type_constructor :
  signature -> Ident.t -> congruence_argument list -> eq_type

val congruence_term_constructor :
  signature -> Ident.t -> congruence_argument list -> eq_term

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

(** An error emitted by the nucleus *)
type error

exception Error of error

(** Print a nucleus error *)
val print_error : penv:print_environment -> error -> Format.formatter -> unit

module Json :
sig
  val abstraction : ('a -> Json.t) -> 'a abstraction -> Json.t

  val is_term : is_term -> Json.t

  val is_type : is_type -> Json.t

  val eq_term : eq_term -> Json.t

  val eq_type : eq_type -> Json.t
end
