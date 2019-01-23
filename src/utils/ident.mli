(** An identifier uniquely determines an entity such as an AML type, or a TT
   rule. Two entities may have the same name (e.g., two instances of type [t]
   each in its own module), and there may be two ways of referring to a single
   identifier (e.g., as [x] inside a module [M] and as [M.x] outside of it). *)

(** The type of identifiers. *)
type t

(** Create a fresh identifier with the given associated name. *)
val create : Name.t -> t

(** Give the name associated with an identifier *)
val name : t -> Name.t

(** Compare two identifiers for equality *)
val equal : t -> t -> bool

(** Compare two identifiers (used to make an instance of [Ord]) *)
val compare : t -> t -> int

(** A map from identifiers to values *)
type 'a map

(** The empty map *)
val empty : 'a map

(** Add a new key-value pair to the map *)
val add : t -> 'a -> 'a map -> 'a map

(** Map the given key to its value, raise [Not_found] if the key is not found *)
val find :  t -> 'a map -> 'a

(** Is the given key bound in the map? *)
val mem : t -> 'a map -> bool

(** Map a function on the values of the map *)
val map : ('a -> 'b) -> 'a map -> 'b map

(** Map a function on the values of the map *)
val mapi : (t -> 'a -> 'b) -> 'a map -> 'b map

(** Give the list of bindings in a map *)
val bindings : 'a map -> (t * 'a) list

(** Print an identifier *)
val print : ?parentheses:bool -> t -> Format.formatter -> unit

module Json :
sig
  val ident : t -> Json.t
end
