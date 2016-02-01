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
val print_term : ?max_level:int -> Name.ident list -> term -> Format.formatter -> unit

(** Print the judgement that something is a type. *)
val print_ty : ?max_level:int -> Name.ident list -> ty -> Format.formatter -> unit

