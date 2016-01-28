module ConstantMap : Map.S with type key = Name.constant
module SignatureMap : Map.S with type key = Name.signature

(** Contains global declarations. *)
type env = private {
  constants : Tt.ty ConstantMap.t;
  signatures : Tt.sig_def SignatureMap.t
}

(** The judgement that the given term has the given type. *)
type term = private Term of Context.t * Tt.term * Tt.ty

(** The judgement that the given term is a type. *)
type ty = private Ty of Context.t * Tt.ty

(** The jdugement that [Type] is a type. *)
val ty_ty : ty

(** The type judgement of a term judgement. *)
val typeof : term -> ty

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

(** Destructors *)
type 'a abstraction = Name.atom * ty * 'a

type signature = Name.signature * (Name.atom, term) Tt.constrain list

type structure = signature * term list

type sig_def = (Name.label * Name.atom * ty) list

type shape =
  | Type
  | Atom of Context.t * Name.atom
  | Constant of Name.ident
  | Prod of ty abstraction
  | Lambda of term abstraction
    (** Apply (j1,j2) means (up to alpha equivalence)
        - j1 = ctx1 |- e1 : forall x: A,B
        - ctx2 |- e2 : A
        - ctx1 and ctx2 joinable *)
  | Apply of term * term
  | Eq of term * term
  | Refl of term
  | Signature of signature
  | Structure of structure
  | Projection of term * Name.label

val shape : loc:Location.t -> env -> term -> shape
val shape_ty : loc:Location.t -> env -> ty -> shape

