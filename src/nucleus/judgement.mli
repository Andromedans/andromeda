(** The judgement that the given term has the given type. *)
type term = Context.t * Tt.term * Tt.ty

(** The judgement that the given term is a type. *)
type ty = Context.t * Tt.ty

(** The judgement that two types are equal. *)
type equal_ty = Context.t * Tt.ty * Tt.ty

(** The jdugement that [Type] is a type. *)
val ty_ty : ty

(** The type judgement of a term judgement. *)
val typeof : term -> ty

(** Create a term judgment. *)
val mk_term : Context.t -> Tt.term -> Tt.ty -> term

(** Create a type judgment. *)
val mk_ty : Context.t -> Tt.ty -> ty

(** Print the judgement that something is a term. *)
val print_term : ?max_level:int -> Name.ident list -> term -> Format.formatter -> unit

(** Print the judgement that something is a type. *)
val print_ty : ?max_level:int -> Name.ident list -> ty -> Format.formatter -> unit


