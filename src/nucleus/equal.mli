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
val equal : Context.t -> Tt.term -> Tt.term -> Tt.ty ->
            Context.t Opt.opt

(** [equal_ty env ctx t1 t2] returns a context [G] that is an extension of
    [ctx] such that the types [t1] and [t2] are equal under [G]. *)
val equal_ty : Context.t -> Tt.ty -> Tt.ty -> Context.t Opt.opt

(** [reduction_step env ctx e] returns a context [ctx'] and a term [e']
    if [e] is a beta redex or a projection of an explicit structure
    such that [e'] is the reduced form
    and [ctx'] contains assumptions necessary for typing annotations to match. *)
val reduction_step : Context.t -> Tt.term -> (Context.t * Tt.term) Opt.opt

(** [congruence env ctx e1 e2 t] calls [equal] on immediate subterms of [e1] and [e2] when
    their toplevel structures match. *)
val congruence : loc:Location.t -> Context.t -> Tt.term -> Tt.term -> Tt.ty ->
                 Context.t Opt.opt

(** [extensionality env ctx e1 e2 t] applies extensionality rules (for equality types,
    products, and signatures). *)
val extensionality : loc:Location.t -> Context.t -> Tt.term -> Tt.term -> Tt.ty ->
                      Context.t Opt.opt

(** Convert a type to an equality type. *)
val as_eq : Jdg.ty -> (Context.t * Tt.ty * Tt.term * Tt.term) Monad.t

(** Convert a type to a product. *)
val as_prod : Jdg.ty -> (Context.t * Tt.ty Tt.ty_abstraction) Monad.t

(** Convert a type to a signature. *)
val as_signature : Jdg.ty -> (Context.t * Name.signature) Monad.t

