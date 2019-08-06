(** Equality checking *)

(** Compares two terms at alpha-equivalent types *)
val equal_term :
  at:Location.t -> Nucleus.signature ->
  Nucleus.is_term -> Nucleus.is_term -> Nucleus.eq_term option Runtime.comp

(** Compare two type abstractions. *)
val equal_type :
  at:Location.t -> Nucleus.is_type -> Nucleus.is_type -> Nucleus.eq_type option Runtime.comp

(** Coerce the given term to the given type, if possible *)
val coerce :
  at:Location.t -> Nucleus.signature -> Nucleus.judgement_abstraction -> Nucleus.boundary_abstraction ->
  Nucleus.judgement_abstraction option Runtime.comp
