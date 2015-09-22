(** The judgement that the given term has the given type. *)
type term = Tt.term * Tt.ty

(** The judgement that the given term is a type. *)
type ty = Tt.ty

(** Create a term judgment. *)
val mk_term : Tt.term -> Tt.ty -> term

(** Create a type judgment. *)
val mk_ty : Tt.ty -> ty

(** Print the judgement that something is a term. *)
val print_term : Name.ident list -> term -> Format.formatter -> unit

(** Print the judgement that something is a type. *)
val print_ty : Name.ident list -> ty -> Format.formatter -> unit


