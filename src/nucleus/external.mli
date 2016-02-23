(** Lookup an external value, if any. *)
val lookup : string -> (Location.t -> Value.value Value.comp) option
