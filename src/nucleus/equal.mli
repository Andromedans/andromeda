(** Equality checking *)

(** Compares 2 terms at alpha-equivalent types *)
val equal : loc:Location.t -> Jdg.term -> Jdg.term -> Jdg.eq_term option Runtime.comp

val equal_ty : loc:Location.t -> Jdg.ty -> Jdg.ty -> Jdg.eq_ty option Runtime.comp

val reduction_step : loc:Location.t -> Jdg.term -> Jdg.eq_term option Runtime.comp

val congruence : loc:Location.t -> Jdg.term -> Jdg.term -> Jdg.eq_term option Runtime.comp

val extensionality : loc:Location.t -> Jdg.term -> Jdg.term -> Jdg.eq_term option Runtime.comp

val as_eq : loc:Location.t -> Jdg.ty -> (Jdg.eq_ty * Jdg.term * Jdg.term) option Runtime.comp

val as_prod : loc:Location.t -> Jdg.ty -> (Jdg.eq_ty * Jdg.atom * Jdg.ty) option Runtime.comp

