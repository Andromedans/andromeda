(** Equality checking and weak-head-normal-forms *)

module Monad : sig
  type +'a t

  val run : 'a t -> ('a*Name.AtomSet.t) Value.result
end

module Opt : sig
  type +'a opt

  val run : 'a opt -> ('a*Name.AtomSet.t) option Value.result
end

(** [equal env ctx e1 e2 t] returns a context [G] that is an extension of [ctx]
    such that the terms [e1] and [e2] of type [t] are equal under [G]. *)
val equal : Value.Env.t -> Context.t -> Tt.term -> Tt.term -> Tt.ty ->
            Context.t Opt.opt

(** [equal_ty env ctx t1 t2] returns a context [G] that is an extension of
    [ctx] such that the types [t1] and [t2] are equal under [G]. *)
val equal_ty : Value.Env.t -> Context.t -> Tt.ty -> Tt.ty -> Context.t Opt.opt

val reduce_step : Value.Env.t -> Context.t -> Tt.term -> (Context.t * Tt.term) Opt.opt

(** [whnf env ctx e] reduces expression [e], assuming that it has a type in context [ctx]. *)
val whnf : Value.Env.t -> Context.t -> Tt.term -> (Context.t * Tt.term) Monad.t

(** [whnf_ty env ctx t] reduces type [t], assuming that it is a type in context [ctx]. *)
val whnf_ty : Value.Env.t -> Context.t -> Tt.ty -> (Context.t * Tt.ty) Monad.t

(** Convert a term to an atom. *)
val as_atom : Value.Env.t -> Judgement.term -> (Context.t * Name.atom * Tt.ty) Monad.t

(** Convert a type to an equality type. *)
val as_eq : Value.Env.t -> Judgement.ty -> (Context.t * Tt.ty * Tt.term * Tt.term) Monad.t

(** Convert a type to a product. *)
val as_prod : Value.Env.t -> Judgement.ty -> (Context.t * Tt.ty Tt.ty_abstraction) Monad.t

(** Convert a type to a universally quantified equality type by aggresively
    unfolding as many inner products as possible. If we get a bare equality type
    the list of binders is empty (and the call succeeds). *)
val as_universal_eq :
  Value.Env.t -> Judgement.ty -> (Context.t * (Tt.ty * Tt.term * Tt.term) Tt.ty_abstraction) Monad.t

(** Convert a type to a universally quantified bracket type, aggresively
    by unfolding as many inner products as possible. If we get something
    that is not a bracket that is ok, we just imagine there was one. *)
val as_universal_bracket :
  Value.Env.t -> Judgement.ty -> (Context.t * Tt.ty Tt.ty_abstraction) Monad.t

(** [inhabit_bracket env t] attempts to inhabit the bracket type [[t]] using inhabit
    hints. It returns [None] on failure or [Some (ctx, Tt.Inhab)] if it succeeded
    inhabiting the bracket type in context [ctx]. *)
val inhabit_bracket :
  subgoals:bool -> loc:Location.t ->
  Value.Env.t -> Judgement.ty -> (Context.t * Tt.term) Opt.opt

(** Convert a type to a bracket type. *)
val as_bracket : Value.Env.t -> Judgement.ty -> (Context.t * Tt.ty) Monad.t

(** Convert a type to a signature. *)
val as_signature : Value.Env.t -> Judgement.ty -> (Context.t * Tt.signature) Monad.t

