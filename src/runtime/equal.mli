(** Equality checking *)

(** Compare two type abstractions. *)
val equal_type :
  at:Location.t -> Nucleus.is_type -> Nucleus.is_type -> Nucleus.eq_type Runtime.comp

(** Coerce the given term to the given type, if possible *)
val coerce :
  at:Location.t -> Nucleus.signature -> Nucleus.judgement_abstraction -> Nucleus.boundary_abstraction ->
  Nucleus.judgement_abstraction Runtime.comp
