(** [equal_ty ctx t1 t2] checks whether types [t1] and [t2] are equal. *)
val equal_ty : Context.t -> Syntax.ty -> Syntax.ty -> bool

(** [as_prod ctx t] decomposes type [t] as a product type, or fails with a
    typing error if it cannot do it. *)
val as_prod : Context.t -> Syntax.ty -> Common.name * Syntax.ty * Syntax.bare_ty
