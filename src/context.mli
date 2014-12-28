(** The type of contexts *)
type t

(** The empty context *)
val empty : t

(** Lookup a free variable. *)
val lookup_free : Common.name -> t -> Value.ty option

(** Lookup a meta variable. *)
val lookup_meta : Common.bound -> t -> Value.value option

(** Is the given name bound as a free variable? *)
val is_bound : Common.name -> t -> bool

(** Add a free variable of a given type to the context.
    Fails if the free variable is already bound. *)
val add_free : Common.name -> Value.ty -> t -> t 

(** Add a meta variable with suggested name to the context. *)
val add_meta : Common.name -> Value.value -> t -> t
