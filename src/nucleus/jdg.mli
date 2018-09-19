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

type stump_is_type =
  | TypeConstructor of Name.constructor * premise list

type stump_is_term =
  | TermAtom of is_type TT.atom
  | TermConstructor of Name.constructor * premise list
  | TermConvert of is_term * eq_type

type stump_eq_type =
  | EqType of TT.assumption * is_type * is_type

type stump_eq_term =
  | EqTerm of TT.assumption * is_term * is_term * is_type

module Signature : sig
  type t

  val empty : t

  val add_constant : Name.constant -> is_type -> t -> t
end

(** Given a type formation rule and a list of premises, match the rule
   against the given premises, make sure they fit the rule, and return the
   judgement corresponding to the conclusion of the rule. *)
val form_is_type : Rule.is_type -> premise list -> is_type

(** Given a term rule and a list of premises, match the rule against the given
   premises, make sure they fit the rule, and return the list of arguments that the term
   constructor should be applied to, together with the natural type of the resulting term.
 *)
val form_is_term : Rule.is_term -> premise list -> TT.argument list * TT.ty

(** Given an equality type rule and a list of premises, match the rule against the given
   premises, make sure they fit the rule, and return the conclusion of the instance of the rule
   so obtained. *)
val form_eq_type : Rule.eq_type -> premise list -> TT.ty * TT.ty

(** Given an terms equality type rule and a list of premises, match the rule
   against the given premises, make sure they fit the rule, and return the conclusion of
   the instance of the rule so obtained. *)
val form_eq_term : Rule.eq_term -> premise list -> TT.term * TT.term * TT.ty

(** Given a term judgment and the arguments of the corresponding term constructor, match
   the arguments against the rule to invert them to the premises of the rule, as well as
   to the natural type of the conclusion. *)
val invert_is_term : Rule.is_term -> TT.argument list -> premise list * TT.ty

(** Given a type judgment and the arguments of the corresponding term constructor, match
   the arguments against the rule to invert them to the premises of the rule. *)
val invert_is_type : Rule.is_type -> TT.argument list -> premise list

(** An error emitted by the nucleus *)
type error

exception Error of error

(** Print a nucleus error *)
val print_error : penv:TT.print_env -> error -> Format.formatter -> unit

(** The type judgement of a term judgement. *)
val typeof : is_term -> is_type

(** Typeof for atoms *)
val atom_is_type : is_atom -> is_type

(** Convert atom judgement to term judgement *)
val atom_is_term : is_atom -> is_term

(** Does this atom occur in this judgement, and if so with what type? *)
val occurs : is_atom -> is_term -> is_atom option

(** The context associated with a term judgement. *)
val contextof : is_term -> is_atom list

(** Print the judgement that something is a term. *)
val print_is_term : penv:TT.print_env -> ?max_level:Level.t -> is_term -> Format.formatter -> unit

(** Print the judgement that something is a type. *)
val print_is_type : penv:TT.print_env -> ?max_level:Level.t -> is_type -> Format.formatter -> unit

(** Print the judgement that terms are equal. *)
val print_eq_term : penv:TT.print_env -> ?max_level:Level.t -> eq_term -> Format.formatter -> unit

(** Print the judgement that types are equal. *)
val print_eq_type : penv:TT.print_env -> ?max_level:Level.t -> eq_type -> Format.formatter -> unit

(** Destructors *)

(* Inversion principles *)
val invert_is_term : is_term -> stump_is_term
val invert_is_type : is_type -> stump_is_type
val invert_eq_type : eq_type -> TT.assumption * is_type * is_type
val invert_eq_term : eq_term -> TT.assumption * is_term * is_term * is_type

(** Deconstruct a type judgment into a type abstraction, if possible. *)
val invert_abstract_ty : is_type -> (is_atom * is_type) option

(** Construct a term judgement using the appropriate formation rule. The type is the natural type. *)
val form_is_term : Signature.t -> stump_is_term -> is_term

(** Construct a type judgement using the appropriate formation rule. *)
val form_is_type : Signature.t -> stump_is_type -> is_type

(** Substitution *)

(** [substitute_ty t a v] substitutes [a] with [v] in [t]. *)
val substitute_ty : is_atom -> is_term -> is_type -> is_type

(** [substitute e a v] substitutes [a] with [v] in [e]. *)
val substitute : is_term -> is_atom -> is_term -> is_term

(** Conversion *)

(** Destructors *)

(** If [e1 == e2 : A] and [A == B] then [e1 == e2 : B] *)
val convert_eq_term : eq_term -> eq_type -> eq_term

(** Constructors *)

(** Construct the judgment [e == e : A] from [e : A] *)
val reflexivity : is_term -> eq_term

(** Construct the jdugment [A == A] from [A type] *)
val reflexivity_ty : is_type -> eq_type

(** Given two terms [e1 : A1] and [e2 : A2] construct [e1 == e2 : A1],
    provided [A1] and [A2] are alpha equal and [e1] and [e2] are alpha equal *)
val mk_alpha_equal : is_term -> is_term -> eq_term option

(** Given two types [A] and [B] construct [A == B] provided the types are alpha equal *)
val mk_alpha_equal_ty : is_type -> is_type -> eq_type option

(** Test whether terms are alpha-equal. They may have different types and incompatible contexts even if [true] is returned. *)
val alpha_equal_is_term : is_term -> is_term -> bool

(** Test whether types are alpha-equal. They may have different contexts. *)
val alpha_equal_is_type : is_type -> is_type -> bool

(** Form an equality of two alpha-equal types. They must also have compatible contexts. *)
val alpha_equal_eq_type : is_type -> is_type -> eq_type option

(** If [e1 == e2 : A] then [e2 == e1 : A] *)
val symmetry_term : eq_term -> eq_term

(** If [A == B] then [B == A] *)
val symmetry_type : eq_type -> eq_type

(** If [e1 == e2 : A] and [e2 == e3 : A] then [e1 == e2 : A] *)
val transitivity_term : eq_term -> eq_term -> eq_term

(** If [A == B] and [B == C] then [A == C] *)
val transitivity_type : eq_type -> eq_type -> eq_type

(** Congruence rules *)

(** If [A1 == A2] and [B1 == B2] then [{x : A1} B1 == {x : A2} B2].
    The first atom is used to abstract both sides. The second is used only for the name in the right hand side product. *)
val congr_abstract_type : eq_type -> is_atom -> is_atom -> eq_type -> eq_type

(** If [A1 == A2], [B1 == B2] and [e1 == e2 : B1] then [{x : A1} (e1 : B1) == {x : A2} (e2 : B2) : {x : A1} B1].
    The first atom is used to abstract both sides. The second is used only for the name in the right hand side. *)
val congr_abstract_term : eq_type -> is_atom -> is_atom -> eq_type -> eq_term -> eq_term

(** Derivable rules *)

module Json :
sig
  val is_term : is_term -> Json.t

  val is_type : is_type -> Json.t

  val eq_term : eq_term -> Json.t

  val eq_type : eq_type -> Json.t
end
