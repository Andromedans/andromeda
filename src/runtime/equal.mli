(** Equality checking *)

(** Compares two terms at alpha-equivalent types *)
val equal : loc:Location.t -> Jdg.term -> Jdg.term -> Jdg.eq_term option Runtime.comp

val equal_ty : loc:Location.t -> Jdg.ty -> Jdg.ty -> Jdg.eq_ty option Runtime.comp

(** Coerce the given term to the given type, if possible *)
val coerce : loc:Location.t -> Jdg.term -> Jdg.ty -> Jdg.term option Runtime.comp

(** Coerce the given term to a term of a product type, if possible *)
val coerce_fun : loc:Location.t -> Jdg.term -> (Jdg.term * Jdg.atom * Jdg.ty) option Runtime.comp

val reduction_step : loc:Location.t -> Jdg.term -> Jdg.eq_term option Runtime.comp

val as_eq : loc:Location.t -> Jdg.ty -> (Jdg.eq_ty * Jdg.term * Jdg.term) option Runtime.comp

val as_prod : loc:Location.t -> Jdg.ty -> (Jdg.eq_ty * Jdg.atom * Jdg.ty) option Runtime.comp

