(** Equality checking and weak-head-normal-forms *)

(** [equal env ctx e1 e2 t] returns a context [G] that is an extension of [ctx]
    such that the terms [e1] and [e2] of type [t] are equal under [G]. *)
val equal : Environment.t -> Context.t -> Tt.term -> Tt.term -> Tt.ty ->
            Context.t option Value.result

(** [equal_ty env ctx t1 t2] returns a context [G] that is an extension of
    [ctx] such that the types [t1] and [t2] are equal under [G]. *)
val equal_ty : Environment.t -> Context.t -> Tt.ty -> Tt.ty -> Context.t option Value.result

(** [whnf env ctx e] reduces expression [e], assuming that it has a type in context [ctx]. *)
val whnf : Environment.t -> Context.t -> Tt.term -> (Context.t * Tt.term) Value.result

(** [whnf_ty env ctx t] reduces type [t], assuming that it is a type in context [ctx]. *)
val whnf_ty : Environment.t -> Context.t -> Tt.ty -> (Context.t * Tt.ty) Value.result

(** [snf env ctx e] reduces expression [e] to strong normal form, assuming that it has a type in context [ctx]. *)
val snf : Environment.t -> Context.t -> Tt.term -> (Context.t * Tt.term) Value.result

(** [whnf_ty env ctx t] reduces type [t] to strong normal form, assuming that it is a type in context [ctx]. *)
val snf_ty : Environment.t -> Context.t -> Tt.ty -> (Context.t * Tt.ty) Value.result

(** Convert a term to an atom. *)
val as_atom : Environment.t -> Judgement.term -> (Context.t * Name.atom * Tt.ty) Value.result

(** Convert a type to an equality type. *)
val as_eq : Environment.t -> Judgement.ty -> (Context.t * Tt.ty * Tt.term * Tt.term) Value.result

(** Convert a type to a product. *)
val as_prod : Environment.t -> Judgement.ty -> (Context.t * Tt.ty Tt.ty_abstraction) Value.result

(** Convert a type to a universally quantified equality type by aggresively
    unfolding as many inner products as possible. If we get a bare equality type
    the list of binders is empty (and the call succeeds). *)
val as_universal_eq :
  Environment.t -> Judgement.ty -> (Context.t * (Tt.ty * Tt.term * Tt.term) Tt.ty_abstraction) Value.result

(** Convert a type to a universally quantified bracket type, aggresively
    by unfolding as many inner products as possible. If we get something
    that is not a bracket that is ok, we just imagine there was one. *)
val as_universal_bracket :
  Environment.t -> Judgement.ty -> (Context.t * Tt.ty Tt.ty_abstraction) Value.result

(** [inhabit_bracket env t] attempts to inhabit the bracket type [[t]] using inhabit
    hints. It returns [None] on failure or [Some (ctx, Tt.Inhab)] if it succeeded
    inhabiting the bracket type in context [ctx]. *)
val inhabit_bracket :
  subgoals:bool -> loc:Location.t ->
  Environment.t -> Judgement.ty -> (Context.t * Tt.term) option Value.result

(** Convert a type to a bracket type. *)
val as_bracket : Environment.t -> Judgement.ty -> (Context.t * Tt.ty) Value.result

(** Convert a type to a signature. *)
val as_signature : Environment.t -> Judgement.ty -> (Context.t * Tt.signature) Value.result

