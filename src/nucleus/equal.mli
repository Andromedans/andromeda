(** Equality checking and weak-head-normal-forms *)

(** A value along with a set of assumptions verifying some implied equality. *)
type 'a witness = ('a * Name.AtomSet.t) Runtime.comp

(** When the equality is not guaranteed to hold. *)
type 'a opt = ('a * Name.AtomSet.t) option Runtime.comp

(** [equal env ctx e1 e2 t] returns a Jdg.Ctx [G] that is an extension of [ctx]
    such that the terms [e1] and [e2] of type [t] are equal under [G]. *)
val equal : Jdg.Ctx.t -> Tt.term -> Tt.term -> Tt.ty ->
            Jdg.Ctx.t opt

(** [equal_ty env ctx t1 t2] returns a Jdg.Ctx [G] that is an extension of
    [ctx] such that the types [t1] and [t2] are equal under [G]. *)
val equal_ty : Jdg.Ctx.t -> Tt.ty -> Tt.ty -> Jdg.Ctx.t opt

(** [reduction_step env ctx e] returns a Jdg.Ctx [ctx'] and a term [e']
    if [e] is a beta redex or a projection of an explicit structure
    such that [e'] is the reduced form
    and [ctx'] contains assumptions necessary for typing annotations to match. *)
val reduction_step : Jdg.Ctx.t -> Tt.term -> (Jdg.Ctx.t * Tt.term) opt

(** [congruence env ctx e1 e2 t] calls [equal] on immediate subterms of [e1] and [e2] when
    their toplevel structures match. *)
val congruence : loc:Location.t -> Jdg.Ctx.t -> Tt.term -> Tt.term -> Tt.ty ->
                 Jdg.Ctx.t opt

(** [extensionality env ctx e1 e2 t] applies extensionality rules (for equality types,
    products, and signatures). *)
val extensionality : loc:Location.t -> Jdg.Ctx.t -> Tt.term -> Tt.term -> Tt.ty ->
                      Jdg.Ctx.t opt

(** Convert a type to an equality type. *)
val as_eq : Jdg.ty -> (Jdg.Ctx.t * Tt.ty * Tt.term * Tt.term) witness

(** Convert a type to a product. *)
val as_prod : Jdg.ty -> (Jdg.Ctx.t * Tt.ty Tt.ty_abstraction) witness

