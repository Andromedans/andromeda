(** Equality checking and weak-head-normal-forms *)

(** [alpha_equal_ty t1 t2] returns [true] if types [t1] and [t2] are
	alpha equal. *)
val alpha_equal_ty: Tt.ty -> Tt.ty -> bool

(** [equal ctx e1 e2 t] checks whether terms [e1] and [e2] of type [t] are equal. *)
val equal : Context.t -> Tt.term -> Tt.term -> Tt.ty -> bool

(** [equal_ty ctx t1 t2] checks whether types [t1] and [t2] are equal. *)
val equal_ty : Context.t -> Tt.ty -> Tt.ty -> bool

(** Convert a type to a product, failing if it is not a product. *)
val as_prod : Context.t -> Tt.ty -> (Tt.ty, Tt.ty) Tt.abstraction option

(** Convert a type to a product aggresively by unfolding as many inner
    products as possible. If we get something that is not a product,
    the list of binders is empty (and the call succeeds). *)
val as_deep_prod : Context.t -> Tt.ty -> (Tt.ty, Tt.ty) Tt.abstraction

val as_spine : Context.t -> Tt.term -> (Tt.term * (Tt.term * Tt.ty, Tt.ty) Tt.abstraction) option

val as_eq : Context.t -> Tt.term -> (Tt.ty * Tt.term * Tt.term) option

val as_refl : Context.t -> Tt.term -> (Tt.ty * Tt.term) option