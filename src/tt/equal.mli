(** Equality checking and weak-head-normal-forms *)

(** [alpha_equal_ty t1 t2] returns [true] if types [t1] and [t2] are
	alpha equal. *)
val alpha_equal_ty: Tt.ty -> Tt.ty -> bool

(** [equal ctx e1 e2 t] checks whether terms [e1] and [e2] of type [t] are equal. *)
val equal : Context.t -> Tt.term -> Tt.term -> Tt.ty -> bool

(** [equal_ty ctx t1 t2] checks whether types [t1] and [t2] are equal. *)
val equal_ty : Context.t -> Tt.ty -> Tt.ty -> bool

(** Convert a type to a product. *)
val as_prod : Context.t -> Tt.ty -> (Tt.ty, Tt.ty) Tt.abstraction option

(** Convert a type to a bracket type. *)
val as_bracket : Context.t -> Tt.ty -> Tt.ty option

(** Convert a type to a universally quantified equality type by aggresively
    unfolding as many inner products as possible. If we get a bare equality type
    the list of binders is empty (and the call succeeds). *)
val as_universal_eq : Context.t -> Tt.ty -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction

(** Convert a type to a universally quantified bracket type, aggresively
    by unfolding as many inner products as possible. If we get something
    that is not a bracket that is ok, we just imagine there was one. *)
val as_universal_bracket : Context.t -> Tt.ty -> (Tt.ty, Tt.ty) Tt.abstraction

(** [inhabit_bracket ctx t] attempts to inhabit the bracket type [[t]] using
    inhabit hints. *)
val inhabit_bracket : Context.t -> Tt.ty -> Tt.term option