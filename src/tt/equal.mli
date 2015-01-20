(** Equality checking and weak-head-normal-forms *)

(** [alpha_equal_ty t1 t2] returns [true] if types [t1] and [t2] are
	alpha equal. *)
val alpha_equal_ty: Tt.ty -> Tt.ty -> bool

(** [equal_ty ctx t1 t2] checks whether types [t1] and [t2] are equal. *)
val equal_ty : Context.t -> Tt.ty -> Tt.ty -> bool

(** Convert a type to a product *)
val as_prod : Context.t -> Tt.ty -> (Tt.ty, Tt.ty) Tt.abstraction
