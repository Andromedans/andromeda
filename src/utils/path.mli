(** An access path is a reference to a named entity in a module. *)
type t

(** Refer to an entity directly by its identifier. This is used access is made
   in the scope of the entity, i.e. we are referring to [x] from within the
   module in which [x] is defined. *)
val mk_direct : Ident.t -> t

(** make an access path to the entity in the given module via the given name *)
val mk_module : Ident.t -> Name.t -> t

(** compare two paths for equality *)
val equal : t -> t -> bool

(** print a path *)
val print : t -> Format.formatter -> unit
