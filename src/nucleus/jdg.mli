type ctx

(** Judgements [ctx |- e : t] *)
type term

(** Judgements [(x : t) in ctx] *)
type atom

(** Judgements [ctx |- t type] *)
type ty

(** Judgements [|- t type] *)
type closed_ty

(** Judgements [ctx |- e1 == e2 : t] *)
type eq_term

(** Judgements [ctx |- t1 == t2] *)
type eq_ty

module Ctx : sig
  (** The type of contexts. *)
  type t = ctx

  val add_fresh : ty -> Name.ident -> atom

  (** [elements ctx] returns the elements of [ctx] sorted into a list so that all dependencies
      point forward in the list, ie the first atom does not depend on any atom, etc. *)
  val elements : t -> atom list

end

module Env : sig
  type t

  val empty : t

  val add_constant : Name.constant -> closed_ty -> t -> t
end

type error

exception Error of error Location.located

val print_error : penv:Tt.print_env -> error -> Format.formatter -> unit

(** The jdugement that [Type] is a type. *)
val ty_ty : ty

val is_closed_ty : loc:Location.t -> ty -> closed_ty

(** The type judgement of a term judgement. *)
val typeof : term -> ty

(** Typeof for atoms *)
val atom_ty : atom -> ty

(** Convert atom judgement to term judgement *)
val atom_term : loc:Location.t -> atom -> term

(** The judgement ctx |- t : Type associated with ctx |- t type *)
val term_of_ty : ty -> term

(** Strengthening *)
val strengthen : term -> term

val strengthen_ty : ty -> ty

(** Does this atom occur in this judgement, and if so with what type? *)
val occurs : atom -> term -> atom option

val contextof : term -> Ctx.t

(** Print the judgement that something is a term. *)
val print_term : penv:Tt.print_env -> ?max_level:Level.t -> term -> Format.formatter -> unit

(** Print the judgement that something is a type. *)
val print_ty : penv:Tt.print_env -> ?max_level:Level.t -> ty -> Format.formatter -> unit

val print_eq_term : penv:Tt.print_env -> ?max_level:Level.t -> eq_term -> Format.formatter -> unit

val print_eq_ty : penv:Tt.print_env -> ?max_level:Level.t -> eq_ty -> Format.formatter -> unit

(** Destructors *)
(** The atom is used in the second component *)
type 'a abstraction = atom * 'a

(** Contains enough information to construct a new judgement *)
type shape =
  | Type
  | Atom of atom
  | Constant of Name.constant
  | Prod of ty abstraction
  | Lambda of term abstraction
    (** Apply (j1,j2) means (up to alpha equivalence)
        - j1 = ctx1 |- e1 : forall x: A,B
        - j2 = ctx2 |- e2 : A
        - ctx1 and ctx2 joinable *)
  | Apply of term * term
  | Eq of term * term
  | Refl of term

val shape : term -> shape
val shape_ty : ty -> shape

(** Construct a judgement using the appropriate formation rule. The type is the natural type. *)
val form : loc:Location.t -> Env.t -> shape -> term

(** Fails if the type isn't [Type] *)
val is_ty : loc:Location.t -> term -> ty

(** [is_ty ∘ form] *)
val form_ty : loc:Location.t -> Env.t -> shape -> ty

(** Substitution *)

(** [substitute_ty t a v] substitutes [a] with [v] in [t]. *)
val substitute_ty : loc:Location.t -> ty -> atom -> term -> ty

(** [substitute e a v] substitutes [a] with [v] in [e]. *)
val substitute : loc:Location.t -> term -> atom -> term -> term

(** Conversion *)

(** Destructors *)
type side = LEFT | RIGHT

val eq_term_side : side -> eq_term -> term

val eq_term_at_ty : eq_term -> ty

val eq_ty_side : side -> eq_ty -> ty

(** The conversion rule: if [e : A] and [A == B] then [e : B] *)
val convert : loc:Location.t -> term -> eq_ty -> term

(** If [e1 == e2 : A] and [A == B] then [e1 == e2 : B] *)
val convert_eq : loc:Location.t -> eq_term -> eq_ty -> eq_term

(** Constructors *)

val reflexivity : term -> eq_term

val reflexivity_ty : ty -> eq_ty

(** Test whether 2 terms are alpha-equal. They may have different types and incompatible contexts even if [true] is returned. *)
val alpha_equal : term -> term -> bool

(** Compare 2 terms up to alpha equality. They must have alpha-equivalent types and compatible contexts. *)
val alpha_equal_eq_term : loc:Location.t -> term -> term -> eq_term option

(** Compare 2 types up to alpha-equality. They must have compatible contexts. *)
val alpha_equal_eq_ty : loc:Location.t -> ty -> ty -> eq_ty option

val symmetry_ty : eq_ty -> eq_ty

val is_type_equality : eq_term -> eq_ty

(** The reflection rule *)
val reflect : term -> eq_term

(** Beta reduction *)

(** If [A1 == A2], [B1 == B2], [e1 : B1] and [e2 : A2] then [(lambda A1 B1 e1) @[A2 B2] e2 == e1[e2] : B2[e2]]. *)
val beta : loc:Location.t -> eq_ty -> atom -> atom -> eq_ty -> term -> term -> eq_term

(** Congruence rules *)

(** If [A1 == A2] and [B1 == B2] then [prod A1 B1 == prod A2 B2].
    The first atom is used to abstract both sides. The second is used only for the name in the right hand side product. *)
val congr_prod : loc:Location.t -> ?at_ty:eq_ty -> eq_ty -> atom -> atom -> eq_ty -> eq_term

val congr_prod_ty : loc:Location.t -> eq_ty -> atom -> atom -> eq_ty -> eq_ty

(** If [A1 == A2], [B1 == B2] and [e1 == e2 : B1] then [lambda A1. B1. e1 == lambda A2. B2. e2 : prod A1 B1].
    The first atom is used to abstract both sides. The second is used only for the name in the right hand side. *)
val congr_lambda : loc:Location.t -> ?at_ty:eq_ty -> eq_ty -> atom -> atom -> eq_ty -> eq_term -> eq_term

(** If [A1 == A2], [B1 == B2], [h1 == h2 : prod A1 B1] and [e1 == e2 : A1], then [h1 @ [A1 . B1] e1 == h2 @ [A2 . B2] e2 : B1[e1]].
    The first atom is used to abstract both sides. The second is used only for the name in the right hand side. *)
val congr_apply : loc:Location.t -> ?at_ty:eq_ty -> eq_ty -> atom -> atom -> eq_ty -> eq_term -> eq_term -> eq_term

(** If [A == B], [lhs1 == lhs2 : A] and [rhs1 == rhs2 : A] then [Eq A lhs1 rhs1 == Eq B lhs2 rhs2]. *)
val congr_eq : loc:Location.t -> ?at_ty:eq_ty -> eq_ty -> eq_term -> eq_term -> eq_term
val congr_eq_ty : loc:Location.t -> eq_ty -> eq_term -> eq_term -> eq_ty

(** If [A == B] and [e1 == e2 : A] then [refl A e1 == refl B e2 : Eq A e1 e1] *)
val congr_refl : loc:Location.t -> ?at_ty:eq_ty -> eq_ty -> eq_term -> eq_term

(** Extensionality rules *)

val uip : loc:Location.t -> term -> term -> eq_term

val funext : loc:Location.t -> eq_term -> eq_term

(** Derivable rules *)

(** If [e : B] and [A] is the natural type of [e] then [A == B] *)
val natural_eq : loc:Location.t -> Env.t -> term -> eq_ty

(** if [e == e1] and [e == e2] then [refl e : e1 == e2] *)
val mk_refl : loc:Location.t -> eq_term -> eq_term -> term

(** if [e1 == e2] then [refl e1 : e1 == e2] *)
val refl_of_eq : loc:Location.t -> eq_term -> term

