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

(** A computation that, when run, invokes the [eq_term] operation on the given
    terms (wrapped as ML values), and then returns the resulting term equation if any.
 *)
val operation_equal_term :
  loc:Location.t -> Nucleus.is_term -> Nucleus.is_term -> Nucleus.eq_term option Runtime.comp

(** A computation that, when run, invokes the [eq_type] operation on the given
    terms (wrapped as ML values), and then returns the resulting term equation if any.
 *)
val operation_equal_type :
  loc:Location.t -> Nucleus.is_type -> Nucleus.is_type -> Nucleus.eq_type option Runtime.comp

(** A computation that, when run, invokes the [coerce] operation
    on the given type theory term and desired type, and decodes
    the resulting ML value as a value of the correponding ML type [coercible].
 *)
val operation_coerce :
  loc:Location.t -> Nucleus.judgement_abstraction -> Nucleus.boundary_abstraction -> Nucleus.judgement_abstraction option Runtime.comp

(** A hack which will probably disappear: add an atom to the dynamic variable [hypotheses] *)
val add_abstracting : Nucleus.is_term -> 'a Runtime.comp -> 'a Runtime.comp
