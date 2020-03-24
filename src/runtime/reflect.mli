(** Reflection of ML entities to OCaml, and vice versa *)

(** Runtime computations to invoke operations *)

(** Convert an OCaml list to an ML list *)
val mk_list : Runtime.value list -> Runtime.value

(** Convert an OCaml option to an ML option *)
val mk_option : Runtime.value option -> Runtime.value

(** The valus of [Ml.order] *)
val mlless : Runtime.value
val mlequal : Runtime.value
val mlgreater : Runtime.value

(** Invoke the AML [equal_type] operation on the given types. *)
val operation_equal_type :
  at:Location.t -> Nucleus.is_type -> Nucleus.is_type -> Nucleus.eq_type Runtime.comp

(** Invoke the AML [coerce] operation on the given abstracted judgement and boundary. *)
val operation_coerce :
  at:Location.t -> Nucleus.judgement_abstraction -> Nucleus.boundary_abstraction -> Nucleus.judgement_abstraction Runtime.comp

val eqchk_exception: at:Location.t -> string -> Runtime.value Runtime.comp
