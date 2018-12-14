(** Equality checking *)

(** Compares two terms at alpha-equivalent types *)
val equal :
  loc:Location.t -> Nucleus.signature ->
  Nucleus.is_term -> Nucleus.is_term -> Nucleus.eq_term option Runtime.comp

(** Compare two type abstractions. *)
val equal_type :
  loc:Location.t -> Nucleus.is_type -> Nucleus.is_type -> Nucleus.eq_type option Runtime.comp

(** Coerce the given term to the given type, if possible *)
val coerce :
  loc:Location.t -> Nucleus.signature -> Nucleus.is_term_abstraction -> Nucleus.is_type_abstraction ->
  Nucleus.is_term_abstraction option Runtime.comp
