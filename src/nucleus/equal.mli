(** Equality checking and weak-head-normal-forms *)

(** [alpha_equal_ty t1 t2] returns [true] if types [t1] and [t2] are
	alpha equal. *)
val alpha_equal_ty: Tt.ty -> Tt.ty -> bool

(** [equal env ctx e1 e2 t] checks whether terms [e1] and [e2] of type [t] are equal
    in context [ctx]. *)
val equal : Environment.t -> Context.t -> Tt.term -> Tt.term -> Tt.ty -> bool

(** [equal_ty env ctx t1 t2] checks whether types [t1] and [t2] are equal in
    context [ctx]. *)
val equal_ty : Environment.t -> Context.t -> Tt.ty -> Tt.ty -> bool

(** [whnf env ctx e] reduces expression [e], assuming that it has a type in context [ctx]. *)
val whnf : Environment.t -> Context.t -> Tt.term -> Context.t * Tt.term

(** [whnf_ty env ctx t] reduces type [t], assuming that it is a type in context [ctx]. *)
val whnf_ty : Environment.t -> Context.t -> Tt.ty -> Context.t * Tt.ty

(** Convert a type to an equality type. *)
val as_eq :
  Environment.t -> Judgement.ty -> Context.t * Tt.ty * Tt.term * Tt.term

(** Convert a type to a product. *)
val as_prod : Environment.t -> Judgement.ty -> Context.t * Tt.ty Tt.abstraction

(** Convert a type to a bracket type. *)
val as_bracket : Environment.t -> Judgement.ty -> Context.t * Tt.ty

(** Convert a type to a universally quantified equality type by aggresively
    unfolding as many inner products as possible. If we get a bare equality type
    the list of binders is empty (and the call succeeds). *)
val as_universal_eq :
  Environment.t -> Judgement.ty -> Context.t * (Tt.ty * Tt.term * Tt.term) Tt.abstraction

(** Convert a type to a universally quantified bracket type, aggresively
    by unfolding as many inner products as possible. If we get something
    that is not a bracket that is ok, we just imagine there was one. *)
val as_universal_bracket :
  Environment.t -> Judgement.ty -> Context.t * Tt.ty Tt.abstraction

(** [inhabit_bracket env t] attempts to inhabit the bracket type [[t]] using
    inhabit hints. *)
val inhabit_bracket :
  subgoals:bool -> loc:Location.t ->
  Environment.t -> Judgement.ty -> (Context.t * Tt.term) option
