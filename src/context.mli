type context_entry =
  | Entry_free of Syntax.ty        (* a free name *)
  | Entry_value of Syntax.value    (* a variable bound by a [let] *)

(** The type of contexts *)
type t

val empty : t

val names : t -> Common.name list

val lookup : Common.name -> t -> context_entry option

val is_free : Common.name -> t -> bool

val is_value : Common.name -> t -> bool

val add_free : Common.name -> Syntax.ty -> t -> t

val add_fresh : Common.name -> Syntax.ty -> t -> Syntax.term * t

val add_value : Common.name -> Syntax.value -> t -> t

val print : t -> unit
