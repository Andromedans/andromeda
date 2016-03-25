type ctx

(** The judgement that the given term has the given type. *)
type term = private Term of ctx * Tt.term * Tt.ty

(** Special judgement for atoms *)
type atom = private JAtom of ctx * Name.atom * Tt.ty

(** The judgement that the given term is a type. *)
type ty = private Ty of ctx * Tt.ty

type eq_term

type eq_ty

module Ctx : sig
  (** The type of contexts. *)
  type t = ctx

  (** The empty context. *)
  val empty : t

  (** Is the context empty? *)
  val is_empty : t -> bool

  (** Print the context. Atoms are printed according to the environment. *)
  val print : penv:Tt.print_env -> t -> Format.formatter -> unit

  val lookup_atom : Name.atom -> t -> atom option

  (** [is_subset ctx yts] returns [true] if the nodes of [ctx] are a subset of [yts]. *)
  val is_subset : t -> (Name.atom * Tt.ty) list -> bool

  val add_fresh : ty -> Name.ident -> atom

  val recursive_assumptions : t -> Name.AtomSet.t -> Name.AtomSet.t

  val restrict : t -> Name.AtomSet.t -> t

  (** [abstract ctx x t] removes atom [x] from context [ctx].
      It verifies that in [ctx] the atom [x] has type [t] (using alpha equality)
      and that no atom depends on [x].
  *)
  val abstract : loc:Location.t -> t -> Name.atom -> Tt.ty -> t

  (** Join two contexts into a single one.
      Types of common atoms need to be alpha equal.
      The dependencies from the first context are used when both atoms are present. *)
  val join : loc:Location.t -> t -> t -> t

  (** [substitute x (ctx,e,ty)] replaces [x] in [ctx] by [e].
      It assumes that the type of [x] in [ctx] is equal to [ty]. *)
  val substitute : loc:Location.t -> Name.atom -> t * Tt.term * Tt.ty -> t

  (** [elements ctx] returns the elements of [ctx] sorted into a list so that all dependencies
      point forward in the list, ie the first atom does not depend on any atom, etc. *)
  val elements : t -> atom list

end

module Env : sig
  type t

  val empty : t

  val constant_type : Name.constant -> t -> Tt.ty

  val add_constant : Name.constant -> Tt.ty -> t -> t
end

type error

exception Error of error Location.located

val print_error : penv:Tt.print_env -> error -> Format.formatter -> unit

(** The jdugement that [Type] is a type. *)
val ty_ty : ty

(** The type judgement of a term judgement. *)
val typeof : term -> ty

(** Typeof for atoms *)
val atom_ty : atom -> ty

(** Convert atom judgement to term judgement *)
val atom_term : loc:Location.t -> atom -> term

(** The judgement ctx |- t : Type associated with ctx |- t type *)
val term_of_ty : ty -> term

(** Create a term judgment. *)
val mk_term : Ctx.t -> Tt.term -> Tt.ty -> term

(** Create a type judgment. *)
val mk_ty : Ctx.t -> Tt.ty -> ty

(** Strengthening *)
val strengthen : term -> term

(** Print the judgement that something is a term. *)
val print_term : penv:Tt.print_env -> ?max_level:Level.t -> term -> Format.formatter -> unit

(** Print the judgement that something is a type. *)
val print_ty : penv:Tt.print_env -> ?max_level:Level.t -> ty -> Format.formatter -> unit

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

val shape : loc:Location.t -> term -> shape
val shape_ty : loc:Location.t -> ty -> shape

(** Construct a judgement using the appropriate formation rule. The type is the natural type. *)
val form : loc:Location.t -> Env.t -> shape -> term

(** Fails if the type isn't [Type] *)
val is_ty : loc:Location.t -> term -> ty

(** [is_ty ∘ form] *)
val form_ty : loc:Location.t -> Env.t -> shape -> ty


(** Conversion *)

type side = LEFT | RIGHT

val eq_term_side : side -> eq_term -> term

val eq_term_at_ty : eq_term -> ty

val eq_ty_side : side -> eq_ty -> ty

val eq_term_alpha : term -> eq_term

val eq_ty_alpha : ty -> eq_ty

(** Derivable rules *)

(** if [e == e1] and [e == e2] then [refl e : e1 == e2] *)
val mk_refl : loc:Location.t -> eq_term -> eq_term -> term

