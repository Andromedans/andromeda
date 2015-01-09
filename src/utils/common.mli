(** Names of free variables *)
type name

(** Bound variables *)
type bound = int

val anonymous : name

val to_name : string -> name

val to_string : name -> string

val fresh : name -> name

(** Comparison of free variables *)
val eqname : name -> name -> bool

val index_of : int -> name -> name list -> int option

val rindex_of : int -> name -> name list -> int option

val print_name : name -> Format.formatter -> unit
