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

(** An argument to a term or type constructor *)
type premise =
  | PremiseIsType of is_type abstraction
  | PremiseIsTerm of is_term abstraction
  | PremiseEqType of eq_type abstraction
  | PremiseEqTerm of eq_term abstraction

(** A stump is obtained when we invert a judgement. *)

type assumption = is_type Assumption.t

type stump_is_type =
  | TypeConstructor of Name.constructor * premise list

type stump_is_term =
  | TermAtom of is_atom
  | TermConstructor of Name.constructor * premise list
  | TermConvert of is_term * eq_type

type stump_eq_type =
  | EqType of assumption * is_type * is_type

type stump_eq_term =
  | EqTerm of assumption * is_term * is_term * is_type

type 'a stump_abstraction =
  | NotAbstract of 'a
  | Abstract of is_atom * 'a abstraction


(** An auxiliary type for providing arguments to a congruence rule. Each arguments is like
   two endpoints with a path between them, except that no paths between equalities are
   needed. *)
type congruence_premise =
  | CongrIsType of is_type abstraction * is_type abstraction * eq_type abstraction
  | CongrIsTerm of is_term abstraction * is_term abstraction * eq_term abstraction
  | CongrEqType of eq_type abstraction * eq_type abstraction
  | CongrEqTerm of eq_term abstraction * eq_term abstraction


module Signature : sig
  type t

  val empty : t
end

(** Given a type formation rule and a list of premises, match the rule
   against the given premises, make sure they fit the rule, and return the
   judgement corresponding to the conclusion of the rule. *)
val form_is_type_rule : Signature.t -> Name.constructor -> premise list -> is_type

(** Given a term rule and a list of premises, match the rule against the given
    premises, make sure they fit the rule, and return the list of arguments that
    the term constructor should be applied to, together with the natural type of
    the resulting term. *)
val form_is_term_rule : Signature.t -> Name.constructor -> premise list -> is_term

(** Convert atom judgement to term judgement *)
val form_is_term_atom : is_atom -> is_term

(** [fresh_atom x t] Create a fresh atom from name [x] with type [t] *)
val fresh_atom : Name.ident -> is_type -> is_atom

val form_is_term_convert : Signature.t -> is_term -> eq_type -> is_term

(** Given an equality type rule and a list of premises, match the rule against
    the given premises, make sure they fit the rule, and return the conclusion
    of the instance of the rule so obtained. *)
val form_eq_type_rule : Signature.t -> Name.constructor -> premise list -> eq_type

(** Given an terms equality type rule and a list of premises, match the rule
    against the given premises, make sure they fit the rule, and return the
    conclusion of the instance of the rule so obtained. *)
val form_eq_term_rule : Signature.t -> Name.constructor -> premise list -> eq_term

(** Form a non-abstracted abstraction *)
val form_not_abstract : 'a -> 'a abstraction

(** Form an abstracted abstraction *)
val form_abstract :
  (Name.atom -> ?lvl:TT.bound -> 'a -> 'a) ->
  TT.ty TT.atom -> 'a TT.abstraction -> 'a TT.abstraction

val invert_is_type : is_type -> stump_is_type

val invert_is_term : Signature.t -> is_term -> stump_is_term

val invert_eq_type : eq_type -> stump_eq_type

val invert_eq_term : eq_term -> stump_eq_term

val invert_is_term_abstraction : is_term abstraction -> is_term stump_abstraction

val invert_is_type_abstraction : is_type abstraction -> is_type stump_abstraction

val invert_eq_type_abstraction : eq_type abstraction -> eq_type stump_abstraction

val invert_eq_term_abstraction : eq_term abstraction -> eq_term stump_abstraction

val context_is_type_abstraction : is_type abstraction -> is_atom list
val context_is_term_abstraction : is_term abstraction -> is_atom list
val context_eq_type_abstraction : eq_type abstraction -> is_atom list
val context_eq_term_abstraction : eq_term abstraction -> is_atom list

(** An error emitted by the nucleus *)
type error

exception Error of error

(** The type judgement of a term judgement. *)
val type_of_term : Signature.t -> is_term -> is_type

(** The type judgement of an abstracted term judgement. *)
val type_of_term_abstraction : Signature.t -> is_term abstraction -> is_type abstraction

(** Typeof for atoms *)
val type_of_atom : is_atom -> is_type

(** Does this atom occur in this judgement? *)
val occurs_is_type_abstraction : is_atom -> is_type abstraction -> bool
val occurs_is_term_abstraction : is_atom -> is_term abstraction -> bool
val occurs_eq_type_abstraction : is_atom -> eq_type abstraction -> bool
val occurs_eq_term_abstraction : is_atom -> eq_term abstraction -> bool

(** [substitute_type t a v] substitutes [v] for [a] in [t]. *)
val substitute_type : is_term -> is_atom -> is_type -> is_type

(** [substitute_term e a v] substitutes [v] for [a] in [e]. *)
val substitute_term : is_term -> is_atom -> is_term -> is_term

(** If [e1 == e2 : A] and [A == B] then [e1 == e2 : B] *)
val convert_eq_term : eq_term -> eq_type -> eq_term

(** Construct the judgment [e == e : A] from [e : A] *)
val reflexivity_term : Signature.t -> is_term -> eq_term

(** Construct the jdugment [A == A] from [A type] *)
val reflexivity_type : is_type -> eq_type

(** Given two terms [e1 : A1] and [e2 : A2] construct [e1 == e2 : A1],
    provided [A1] and [A2] are alpha equal and [e1] and [e2] are alpha equal *)
val mk_alpha_equal_term : Signature.t -> is_term -> is_term -> eq_term option

(** Given two types [A] and [B] construct [A == B] provided the types are alpha equal *)
val mk_alpha_equal_type : is_type -> is_type -> eq_type option

(** Given two abstractions, construct an abstracted equality provided the abstracted entities are alpha equal. *)
val mk_alpha_equal_abstraction :
  ('a -> 'b -> 'c TT.abstraction option) ->
  'a TT.abstraction -> 'b TT.abstraction -> 'c TT.abstraction option

(** Test whether terms are alpha-equal. They may have different types and incompatible contexts even if [true] is returned. *)
val alpha_equal_term : is_term -> is_term -> bool

(** Test whether types are alpha-equal. They may have different contexts. *)
val alpha_equal_type : is_type -> is_type -> bool

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
val natural_type_eq : Signature.t -> is_term -> eq_type

(** Congruence rules *)

val congruence_type_constructor :
  Signature.t -> Name.constructor -> congruence_premise list -> eq_type

val congruence_term_constructor :
  Signature.t -> Name.constructor -> congruence_premise list -> eq_term

val print_is_term :
  ?max_level:Level.t -> penv:TT.print_env -> is_term -> Format.formatter -> unit

val print_is_type :
  ?max_level:Level.t -> penv:TT.print_env -> is_type -> Format.formatter -> unit

val print_eq_term :
  ?max_level:Level.t -> penv:TT.print_env -> eq_term -> Format.formatter -> unit

val print_eq_type :
  ?max_level:Level.t -> penv:TT.print_env -> eq_type -> Format.formatter -> unit

val print_is_term_abstraction :
  ?max_level:Level.t -> penv:TT.print_env -> is_term abstraction -> Format.formatter -> unit

val print_is_type_abstraction :
  ?max_level:Level.t -> penv:TT.print_env -> is_type abstraction -> Format.formatter -> unit

val print_eq_term_abstraction :
  ?max_level:Level.t -> penv:TT.print_env -> eq_term abstraction -> Format.formatter -> unit

val print_eq_type_abstraction :
  ?max_level:Level.t -> penv:TT.print_env -> eq_type abstraction -> Format.formatter -> unit

(** Print a nucleus error *)
val print_error : penv:TT.print_env -> error -> Format.formatter -> unit

module Json :
sig
  val abstraction : ('a -> Json.t) -> 'a abstraction -> Json.t

  val is_term : is_term -> Json.t

  val is_type : is_type -> Json.t

  val eq_term : eq_term -> Json.t

  val eq_type : eq_type -> Json.t
end
