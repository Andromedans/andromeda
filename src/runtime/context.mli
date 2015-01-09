(** The type of contexts *)
type t

(** The empty context *)
val empty : t

(** Known meta variables *)
val metas : t -> Common.name list

(** Lookup a free variable. *)
val lookup_free : Common.name -> t -> Value.ty option

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : Common.bound -> t -> Common.name * Value.ty

(** Lookup a meta variable. *)
val lookup_meta : Common.bound -> t -> Value.value option

(** Is the given name bound as a free variable? *)
val is_bound : Common.name -> t -> bool

(** Add a free variable of a given type to the context.
    Fails if the free variable is already bound. *)
val add_free : Common.name -> Value.ty -> t -> t 

(** [add_fresh x t ctx] adds a fresh free variable with suggested
    name [x] of given type [t] to the context [ctx]. Return the
    actual name and the new context. *)
val add_fresh : Common.name -> Value.ty -> t -> Common.name * t

(** Add a meta variable with suggested name to the context. *)
val add_meta : Common.name -> Value.value -> t -> t

val free_list : t -> (Common.name * Value.ty) list

val print : t -> Format.formatter -> unit
