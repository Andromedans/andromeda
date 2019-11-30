(** Nonces are used to generate fresh atoms and meta variables. *)
type t

(** Create a fresh nonce associated with the  given name. *)
val create : Name.t -> t

(** The name of the given nonce. *)
val name : t -> Name.t

(** Compare nonces for equality. *)
val equal : t -> t -> bool

(** Compare nonces. *)
val compare : t -> t -> int

(** Print a nonce, with or without a leading questionmark.
    Each nonce is guaranteed to printed in a unique way *)
val print : questionmark:bool -> parentheses:bool -> t -> Format.formatter -> unit

(** A map from nonces to values *)
type 'a map

(** The empty map *)
val map_empty : 'a map

(** Add a key-value pair to a map *)
val map_add : t -> 'a -> 'a map -> 'a map

(** Is the map empty? *)
val map_is_empty : 'a map -> bool

(** Does the given key have a value? *)
val map_mem : t -> 'a map -> bool

(** Map a key to its value, raise [Not_found] if not there *)
val map_find : t -> 'a map -> 'a

(** Union two maps *)
val map_union : (t -> 'a -> 'a -> 'a option) -> 'a map -> 'a map -> 'a map

(** Remove a key from the map *)
val map_remove : t -> 'a map -> 'a map

(** The list of key-value pairs of a map *)
val map_bindings : 'a map -> (t * 'a) list

val map_for_all : (t -> 'a -> bool) -> 'a map -> bool

(** A set of nonces *)
type set

(** The empty set of nonces *)
val set_empty : set

(** Is the set empty? *)
val set_is_empty : set -> bool

(** Create a set from a list *)
val set_of_list : t list -> set

(** Add a nonce to a set *)
val set_add : t -> set -> set

(** Test whether a nonce is in a set *)
val set_mem : t -> set -> bool

module Json :
sig
  (** Convert a meta to JSON. *)
  val nonce : t -> Json.t

  (** Convert a map of metas to JSON (dropping the values). *)
  val map : 'a map -> Json.t
end
