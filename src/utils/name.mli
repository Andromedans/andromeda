(** Names of free variables *)
type t

val anonymous : t

val of_string : string -> t

val to_string : t -> string

val fresh : t -> t

(** Comparison of free variables *)
val eq : t -> t -> bool

val index_of : int -> t -> t list -> int option

val rindex_of : int -> t -> t list -> int option

val print : t -> Format.formatter -> unit
