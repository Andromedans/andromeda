(** The hierarchy of universes. *)

type t (* the poset *)

val of_string : string -> t option

val to_string : t -> string

  (** The level at which [Unit] lives. *)
val zero : t

val leq : t -> t -> bool

val eq : t -> t -> bool

val is_fibered : t -> bool

(** The level of at which [Universe a] lives. *)
val succ : t -> t

(** The level at which a product lives. *)
val max : t -> t -> t
