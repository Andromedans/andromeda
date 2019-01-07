(** Initialize the external definitions in the given runtime environment. *)
val init : Desugar.Ctx.t -> unit

(** Lookup an external value, if it exists. *)
val lookup : string -> Runtime.value option
