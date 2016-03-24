module ConstantMap : Map.S with type key = Name.constant

(** Contains global declarations. *)
type env = private {
  constants : Tt.ty ConstantMap.t;
}

val empty : env

(** The judgement that the given term has the given type. *)
type term = private Term of Context.t * Tt.term * Tt.ty

(** Special judgement for atoms *)
type atom = private JAtom of Context.t * Name.atom * Tt.ty

(** The judgement that the given term is a type. *)
type ty = private Ty of Context.t * Tt.ty

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
val mk_term : Context.t -> Tt.term -> Tt.ty -> term

(** Create a type judgment. *)
val mk_ty : Context.t -> Tt.ty -> ty

(** Strengthening *)
val strengthen : term -> term

(** Print the judgement that something is a term. *)
val print_term : penv:Tt.print_env -> ?max_level:Level.t -> term -> Format.formatter -> unit

(** Print the judgement that something is a type. *)
val print_ty : penv:Tt.print_env -> ?max_level:Level.t -> ty -> Format.formatter -> unit

(** Environment *)
val constant_type : Name.constant -> env -> Tt.ty

val add_constant : Name.constant -> Tt.ty -> env -> env

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

val shape : loc:Location.t -> env -> term -> shape
val shape_ty : loc:Location.t -> env -> ty -> shape

(** Construct a judgement using the appropriate formation rule. The type is the natural type. *)
val form : loc:Location.t -> penv:Tt.print_env -> env -> shape -> term

(** Fails if the type isn't [Type] *)
val is_ty : penv:Tt.print_env -> term -> ty

(** [is_ty ∘ form] *)
val form_ty : loc:Location.t -> penv:Tt.print_env -> env -> shape -> ty

