type ctx

(** Judgements [ctx |- e : t] *)
type is_term

(** Judgements [(x : t) in ctx] *)
type is_atom

(** Judgements [ctx |- t type] *)
type is_type

(** Judgements [|- t type] *)
type closed_ty

(** Judgements [ctx |- e1 == e2 : t] *)
type eq_term

(** Judgements [ctx |- t1 == t2] *)
type eq_type

module Ctx : sig
  (** The type of contexts. *)
  type t = ctx

  val add_fresh : is_type -> Name.ident -> is_atom

  (** [elements ctx] returns the elements of [ctx] sorted into a list so that all dependencies
      point forward in the list, ie the first atom does not depend on any atom, etc. *)
  val elements : t -> is_atom list

end

module Signature : sig
  type t

  val empty : t

  val add_constant : Name.constant -> closed_ty -> t -> t
end

type error

exception Error of error Location.located

val print_error : penv:TT.print_env -> error -> Format.formatter -> unit

(** The jdugement that [Type] is a type. *)
val ty_ty : is_type

(** Verify that a type is closed and return it as a closed type. *)
val is_closed_ty : loc:Location.t -> is_type -> closed_ty

(** The type judgement of a term judgement. *)
val typeof : is_term -> is_type

(** Typeof for atoms *)
val atom_is_type : is_atom -> is_type

(** Convert atom judgement to term judgement *)
val atom_is_term : loc:Location.t -> is_atom -> is_term

(** Does this atom occur in this judgement, and if so with what type? *)
val occurs : is_atom -> is_term -> is_atom option

val contextof : is_term -> Ctx.t

(** Print the judgement that something is a term. *)
val print_is_term : penv:TT.print_env -> ?max_level:Level.t -> is_term -> Format.formatter -> unit

(** Print the judgement that something is a type. *)
val print_is_type : penv:TT.print_env -> ?max_level:Level.t -> is_type -> Format.formatter -> unit

(** Print the judgement that terms are equal. *)
val print_eq_term : penv:TT.print_env -> ?max_level:Level.t -> eq_term -> Format.formatter -> unit

(** Print the judgement that types are equal. *)
val print_eq_type : penv:TT.print_env -> ?max_level:Level.t -> eq_type -> Format.formatter -> unit

(** Destructors *)

(** The atom is used in the second component *)
type 'a abstraction = is_atom * 'a

(** An argument to a term or type constructor *)
type argument =
  | ArgIsType of is_type
  | ArgIsTerm of is_term
  | ArgEqType of eq_type
  | ArgEqTerm of eq_term

(** Contains enough information to construct a new judgement *)
type shape_is_term =
  | Atom of is_atom
  | Constant of Name.constant
  | TermConstructor of Name.constructor * argument list
  | Abstract of is_term abstraction

and shape_is_type =
  | Type (* universe *)
  | TyConstructor of Name.constructor * argument list
  | AbstractTy of is_type abstraction
  | El of is_term

(* Inversion principles *)
val invert_is_term : is_term -> shape_is_term
val invert_is_type : is_type -> shape_is_type
val invert_eq_type : eq_type -> is_type * is_type
val invert_eq_term : eq_term -> is_term * is_term * is_type

(** Deconstruct a type judgment into a type abstraction, if possible. *)
val invert_abstract_ty : is_type -> (is_atom * is_type) option

(** Construct a term judgement using the appropriate formation rule. The type is the natural type. *)
val form : loc:Location.t -> Signature.t -> shape_is_term -> is_term

(** Construct a type judgement using the appropriate formation rule. *)
val form_ty : loc:Location.t -> Signature.t -> shape_is_type -> is_type

(** Substitution *)

(** [substitute_ty t a v] substitutes [a] with [v] in [t]. *)
val substitute_ty : loc:Location.t -> is_type -> is_atom -> is_term -> is_type

(** [substitute e a v] substitutes [a] with [v] in [e]. *)
val substitute : loc:Location.t -> is_term -> is_atom -> is_term -> is_term

(** Conversion *)

(** Destructors *)
type side = LEFT | RIGHT

val eq_term_side : side -> eq_term -> is_term

val eq_term_typeof : eq_term -> is_type

val eq_type_side : side -> eq_type -> is_type

(** The conversion rule: if [e : A] and [A == B] then [e : B] *)
val convert : loc:Location.t -> is_term -> eq_type -> is_term

(** If [e1 == e2 : A] and [A == B] then [e1 == e2 : B] *)
val convert_eq : loc:Location.t -> eq_term -> eq_type -> eq_term

(** Constructors *)

(** Construct the judgment [e == e : A] from [e : A] *)
val reflexivity : is_term -> eq_term

(** Construct the jdugment [A == A] from [A type] *)
val reflexivity_ty : is_type -> eq_type

(** Given two terms [e1 : A1] and [e2 : A2] construct [e1 == e2 : A1],
    provided [A1] and [A2] are alpha equal and [e1] and [e2] are alpha equal *)
val mk_alpha_equal : loc:Location.t -> is_term -> is_term -> eq_term option

(** Given two types [A] and [B] construct [A == B] provided the types are alpha equal *)
val mk_alpha_equal_ty : loc:Location.t -> is_type -> is_type -> eq_type option

(** Test whether terms are alpha-equal. They may have different types and incompatible contexts even if [true] is returned. *)
val alpha_equal_is_term : is_term -> is_term -> bool

(** Test whether types are alpha-equal. They may have different contexts. *)
val alpha_equal_is_type : is_type -> is_type -> bool

(** Form an equality of two alpha-equal types. They must also have compatible contexts. *)
val alpha_equal_eq_type : loc:Location.t -> is_type -> is_type -> eq_type option

(** If [e1 == e2 : A] then [e2 == e1 : A] *)
val symmetry_term : eq_term -> eq_term

(** If [A == B] then [B == A] *)
val symmetry_type : eq_type -> eq_type

(** If [e1 == e2 : A] and [e2 == e3 : A] then [e1 == e2 : A] *)
val transitivity_term : loc:Location.t -> eq_term -> eq_term -> eq_term

(** If [A == B] and [B == C] then [A == C] *)
val transitivity_type : loc:Location.t -> eq_type -> eq_type -> eq_type

(** Congruence rules *)

(** If [A1 == A2] and [B1 == B2] then [{x : A1} B1 == {x : A2} B2].
    The first atom is used to abstract both sides. The second is used only for the name in the right hand side product. *)
val congr_abstract_type : loc:Location.t -> eq_type -> is_atom -> is_atom -> eq_type -> eq_type

(** If [A1 == A2], [B1 == B2] and [e1 == e2 : B1] then [{x : A1} (e1 : B1) == {x : A2} (e2 : B2) : {x : A1} B1].
    The first atom is used to abstract both sides. The second is used only for the name in the right hand side. *)
val congr_abstract_term : loc:Location.t -> eq_type -> is_atom -> is_atom -> eq_type -> eq_term -> eq_term

(** Derivable rules *)

(** If [e : B] and [A] is the natural type of [e] then [A == B] *)
val natural_eq_type : loc:Location.t -> Signature.t -> is_term -> eq_type

module Json :
sig
  val is_term : is_term -> Json.t

  val is_type : is_type -> Json.t

  val eq_term : eq_term -> Json.t

  val eq_type : eq_type -> Json.t
end
