(** Access paths to entites in mmodules *)

(** A de Bruijn index *)
type index = Index of Name.t * int

(** A de Bruijn level *)
type level = Level of Name.t * int

(** An access path is a reference to a named entity in a module. *)
type t =
  | Direct of level
  | Module of t * level

(** A set of paths *)
type set

val set_empty : set
val set_add : t -> set -> set
val set_mem : t -> set -> bool

(** Access path to an ML constructor *)
type ml_constructor = t * level

(** Linearly ordering of paths, compatible with [Map.OrderedType] *)
val compare_path : t -> t -> int

(** Compare paths *)
val equal : t -> t -> bool

(** Linearly ordering of levels, compatible with [Map.OrderedType] *)
val compare_level : level -> level -> int

(** A mapping from paths *)
type 'a map

val empty : 'a map
val add : t -> 'a -> 'a map -> 'a map
val find : t -> 'a map -> 'a

(** print a path *)
val print : opens:set -> parentheses:bool -> t -> Format.formatter -> unit

module Json :
sig
  val level : level -> Json.t
  val path : t -> Json.t
end
