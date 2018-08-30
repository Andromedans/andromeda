(** Equality checking *)

(** Compares two terms at alpha-equivalent types *)
val equal : loc:Location.t -> Jdg.is_term -> Jdg.is_term -> Jdg.eq_term option Runtime.comp

val equal_ty : loc:Location.t -> Jdg.is_type -> Jdg.is_type -> Jdg.eq_type option Runtime.comp

(** Coerce the given term to the given type, if possible *)
val coerce : loc:Location.t -> Jdg.is_term -> Jdg.is_type -> Jdg.is_term option Runtime.comp
