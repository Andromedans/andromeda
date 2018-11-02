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

(** A stump is obtained when we invert a judgement. *)

type is_type_boundary = unit abstraction
type is_term_boundary = is_type abstraction
type eq_type_boundary = (is_type * is_type) abstraction
type eq_term_boundary = (is_term * is_term * is_type) abstraction

type boundary =
    | BoundaryType of is_type_boundary
    | BoundaryTerm of is_term_boundary
    | BoundaryEqType of eq_type_boundary
    | BoundaryEqTerm of eq_term_boundary

type assumption

type 'a meta = 'a TT.meta
type is_type_meta = is_type_boundary meta
type is_term_meta = is_term_boundary meta
type eq_type_meta = eq_type_boundary meta
type eq_term_meta = eq_term_boundary meta

type stump_is_type =
  | TypeConstructor of Name.constructor * argument list
  | TypeMeta of is_type_meta * is_term list

type stump_is_term =
  | TermAtom of is_atom
  | TermConstructor of Name.constructor * argument list
  | TermMeta of is_term_meta * is_term list
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
type congruence_argument =
  | CongrIsType of is_type_abstraction * is_type_abstraction * eq_type_abstraction
  | CongrIsTerm of is_term_abstraction * is_term_abstraction * eq_term_abstraction
  | CongrEqType of eq_type_abstraction * eq_type_abstraction
  | CongrEqTerm of eq_term_abstraction * eq_term_abstraction


module Signature : sig
  type t

  val empty : t

  val add_rule_is_type : Name.constructor -> Rule.rule_is_type -> t -> t
  val add_rule_is_term : Name.constructor -> Rule.rule_is_term -> t -> t
  val add_rule_eq_type : Name.constructor -> Rule.rule_eq_type -> t -> t
  val add_rule_eq_term : Name.constructor -> Rule.rule_eq_term -> t -> t

end

val form_rule_is_type :
  (Name.meta * boundary) list -> Rule.rule_is_type

val form_rule_is_term :
  (Name.meta * boundary) list -> TT.ty -> Rule.rule_is_term

val form_rule_eq_type :
  (Name.meta * boundary) list -> TT.ty * TT.ty -> Rule.rule_eq_type

val form_rule_eq_term :
  (Name.meta * boundary) list -> TT.term * TT.term * TT.ty -> Rule.rule_eq_term

(** Given a type formation rule and a list of arguments, match the rule
   against the given arguments, make sure they fit the rule, and return the
   judgement corresponding to the conclusion of the rule. *)
val form_is_type : Signature.t -> Name.constructor -> argument list -> is_type

(** Given a term rule and a list of arguments, match the rule against the given
    arguments, make sure they fit the rule, and return the list of arguments that
    the term constructor should be applied to, together with the natural type of
    the resulting term. *)
val form_is_term : Signature.t -> Name.constructor -> argument list -> is_term

(** Convert atom judgement to term judgement *)
val form_is_term_atom : is_atom -> is_term

(** [form_is_type_meta sgn a args] creates a is_type judgement by applying the
    meta-variable [a] = `x : A, ..., y : B ⊢ jdg` to a list of terms [args] of
    matching types. *)
val form_is_type_meta : Signature.t -> is_type_meta -> is_term list -> is_type

(** [form_is_term_meta sgn a args] creates a is_term judgement by applying the
    meta-variable [a] = `x : A, ..., y : B ⊢ jdg` to a list of terms [args] of
    matching types. *)
val form_is_term_meta : Signature.t -> is_term_meta -> is_term list -> is_term

val form_is_term_convert : Signature.t -> is_term -> eq_type -> is_term

(** Given an equality type rule and a list of arguments, match the rule against
    the given arguments, make sure they fit the rule, and return the conclusion
    of the instance of the rule so obtained. *)
val form_eq_type : Signature.t -> Name.constructor -> argument list -> eq_type

val form_eq_type_meta : Signature.t -> eq_type_meta -> TT.term list -> TT.eq_type

val form_eq_term_meta : Signature.t -> eq_term_meta -> TT.term list -> TT.eq_term

(** Given an terms equality type rule and a list of arguments, match the rule
    against the given arguments, make sure they fit the rule, and return the
    conclusion of the instance of the rule so obtained. *)
val form_eq_term : Signature.t -> Name.constructor -> argument list -> eq_term

(** Form a non-abstracted abstraction *)
val abstract_not_abstract : 'a -> 'a abstraction

(** Form an abstracted abstraction *)
val abstract_is_type : is_atom -> is_type_abstraction -> is_type_abstraction
val abstract_is_term : is_atom -> is_term_abstraction -> is_term_abstraction
val abstract_eq_type : is_atom -> eq_type_abstraction -> eq_type_abstraction
val abstract_eq_term : is_atom -> eq_term_abstraction -> eq_term_abstraction

val abstract_boundary_is_type : is_atom -> is_type_boundary -> is_type_boundary
val abstract_boundary_is_term : is_atom -> is_term_boundary -> is_term_boundary
val abstract_boundary_eq_type : is_atom -> eq_type_boundary -> eq_type_boundary
val abstract_boundary_eq_term : is_atom -> eq_term_boundary -> eq_term_boundary

(** [fresh_atom x t] Create a fresh atom from name [x] with type [t] *)
val fresh_atom : Name.ident -> is_type -> is_atom

(** [fresh_is_type_meta x abstr] creates a fresh type meta-variable of type [abstr] *)
val fresh_is_type_meta : Name.ident -> is_type_boundary -> is_type_meta
val fresh_is_term_meta : Name.ident -> is_term_boundary -> is_term_meta
val fresh_eq_type_meta : Name.ident -> eq_type_boundary -> eq_type_meta
val fresh_eq_term_meta : Name.ident -> eq_term_boundary -> eq_term_meta

val is_type_meta_eta_expanded : is_type_meta -> is_type_abstraction
val is_term_meta_eta_expanded : is_term_meta -> is_term_abstraction
val eq_type_meta_eta_expanded : eq_type_meta -> eq_type_abstraction
val eq_term_meta_eta_expanded : eq_term_meta -> eq_term_abstraction

val invert_is_type : is_type -> stump_is_type

val invert_is_term : Signature.t -> is_term -> stump_is_term

val invert_eq_type : eq_type -> stump_eq_type

val invert_eq_term : eq_term -> stump_eq_term

val atom_name : is_atom -> Name.atom

val invert_is_term_abstraction :
  ?atom_name:Name.ident -> is_term_abstraction -> is_term stump_abstraction

val invert_is_type_abstraction :
  ?atom_name:Name.ident -> is_type_abstraction -> is_type stump_abstraction

val invert_eq_type_abstraction :
  ?atom_name:Name.ident -> eq_type_abstraction -> eq_type stump_abstraction

val invert_eq_term_abstraction :
  ?atom_name:Name.ident -> eq_term_abstraction -> eq_term stump_abstraction

val context_is_type_abstraction : is_type_abstraction -> is_atom list
val context_is_term_abstraction : is_term_abstraction -> is_atom list
val context_eq_type_abstraction : eq_type_abstraction -> is_atom list
val context_eq_term_abstraction : eq_term_abstraction -> is_atom list

(** An error emitted by the nucleus *)
type error

exception Error of error

(** The type judgement of a term judgement. *)
val type_of_term : Signature.t -> is_term -> is_type

(** The type judgement of an abstracted term judgement. *)
val type_of_term_abstraction : Signature.t -> is_term_abstraction -> is_type_abstraction

(** Typeof for atoms *)
val type_of_atom : is_atom -> is_type

(** Does this atom occur in this judgement? *)
val occurs_is_type_abstraction : is_atom -> is_type_abstraction -> bool
val occurs_is_term_abstraction : is_atom -> is_term_abstraction -> bool
val occurs_eq_type_abstraction : is_atom -> eq_type_abstraction -> bool
val occurs_eq_term_abstraction : is_atom -> eq_term_abstraction -> bool

val apply_is_type_abstraction :
  Signature.t -> is_type_abstraction -> is_term -> is_type_abstraction

val apply_is_term_abstraction :
  Signature.t -> is_term_abstraction -> is_term -> is_term_abstraction

val apply_eq_type_abstraction :
  Signature.t -> eq_type_abstraction -> is_term -> eq_type_abstraction

val apply_eq_term_abstraction :
  Signature.t -> eq_term_abstraction -> is_term -> eq_term_abstraction

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
  ('a -> 'b -> 'c option) ->
  'a abstraction -> 'b abstraction -> 'c abstraction option

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
  Signature.t -> Name.constructor -> congruence_argument list -> eq_type

val congruence_term_constructor :
  Signature.t -> Name.constructor -> congruence_argument list -> eq_term

(** Printing routines *)

val print_is_term :
  ?max_level:Level.t -> penv:TT.print_env -> is_term -> Format.formatter -> unit

val print_is_type :
  ?max_level:Level.t -> penv:TT.print_env -> is_type -> Format.formatter -> unit

val print_eq_term :
  ?max_level:Level.t -> penv:TT.print_env -> eq_term -> Format.formatter -> unit

val print_eq_type :
  ?max_level:Level.t -> penv:TT.print_env -> eq_type -> Format.formatter -> unit

val print_is_term_abstraction :
  ?max_level:Level.t -> penv:TT.print_env -> is_term_abstraction -> Format.formatter -> unit

val print_is_type_abstraction :
  ?max_level:Level.t -> penv:TT.print_env -> is_type_abstraction -> Format.formatter -> unit

val print_eq_term_abstraction :
  ?max_level:Level.t -> penv:TT.print_env -> eq_term_abstraction -> Format.formatter -> unit

val print_eq_type_abstraction :
  ?max_level:Level.t -> penv:TT.print_env -> eq_type_abstraction -> Format.formatter -> unit

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
