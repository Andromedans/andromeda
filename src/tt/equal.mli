(** [equal_ty ctx t1 t2] checks whether types [t1] and [t2] are equal. *)
val equal_ty : Context.t -> Tt.ty -> Tt.ty -> bool

(** Convert a type to a product *)
val as_prod : Context.t -> Tt.ty -> Name.t * Tt.ty * Tt.ty