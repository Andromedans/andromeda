(** Typing context and runtime environment *)

(** A typing context with a runtime environment, we refer to it as just context *)
type t

(** The empty context *)
val empty : t

(** Known bound variables *)
val bound_names : t -> Name.t list

(** Variable names already used in the context *)
val used_names : t -> Name.t list

(** Lookup a free variable. *)
val lookup_free : Name.t -> t -> Tt.ty option

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : Syntax.bound -> t -> Value.value

(** Return all beta hints in the context *)
val beta_hints : t -> Pattern.beta_hint list

(** Return all eta hints in the context *)
val eta_hints : t -> Pattern.eta_hint list

(** Return all general hints in the context *)
val hints : t -> Pattern.hint list

(** Return all general hints in the context *)
val inhabit : t -> Pattern.inhabit list

(** Add a free variable of a given type to the context.
    Fails if the free variable is already bound. *)
val add_free : Name.t -> Tt.ty -> t -> t

(** Add a beta hint to the context. *)
val add_beta : Pattern.beta_hint -> t -> t

(** Add an eta hint to the context. *)
val add_eta : Pattern.eta_hint -> t -> t

(** Add a hint to the context. *)
val add_hint : Pattern.hint -> t -> t

(** Add an inhabit hint to the context. *)
val add_inhabit : Pattern.inhabit -> t -> t

(** [add_fresh x t ctx] adds a fresh free variable with suggested
    name [x] of given type [t] to the context [ctx]. Return the
    actual name and the new context. *)
val add_fresh : Name.t -> Tt.ty -> t -> Name.t * t

(** Add a bound variable with given name to the context. *)
val add_bound : Name.t -> Value.value -> t -> t

(** Print free variables in the context *)
val print : t -> Format.formatter -> unit
