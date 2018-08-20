(** Equality checking *)

(** Compares two terms at alpha-equivalent types *)
val equal : loc:Location.t -> Jdg.term -> Jdg.term -> Jdg.eq_term option Runtime.comp

val equal_ty : loc:Location.t -> Jdg.ty -> Jdg.ty -> Jdg.eq_ty option Runtime.comp

(** Coerce the given term to the given type, if possible *)
val coerce : loc:Location.t -> Jdg.term -> Jdg.ty -> Jdg.term option Runtime.comp
