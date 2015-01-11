(** Names of free variables *)
type t

(** An anonymous name that cannot be referenced *)
val anonymous : t

(** Convert a string to a name *)
val of_string : string -> t

(** Convert a name to a string *)
val to_string : t -> string

(** Given a name generate a fresh one guaranteed not to exist. *)
val fresh : t -> t

(** Given a list of names [xs] and a name [x], find a nicely printable
    variant of [x] which does not occur in [xs]. *)
val refresh : t list -> t -> t

(** Compare names *)
val eq : t -> t -> bool

(** [index_of k x xs] finds the location of [x] in list [xs], increased by [k].
	The silly increase thing is there so we don't forget to shift de Bruijn 
	indices when we use [index_of].
*)
val index_of : int -> t -> t list -> int option

(** Like [index_of] but count the position from the end of the list. *)
val rindex_of : int -> t -> t list -> int option

(** Print a name. *)
val print : t -> Format.formatter -> unit
