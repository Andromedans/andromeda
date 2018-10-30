(** Sets of assumptions *)
module BoundSet : Set.S with type elt = int

(** A pair of sets, corresponding to free and bound assumptions *)
type ('a, 'b) t

val empty : ('a, 'b) t

val is_empty : ('a, 'b) t -> bool

val unpack : ('a, 'b) t -> 'a Name.AtomMap.t * 'a Name.MetaMap.t * BoundSet.t

val mem_atom : Name.atom -> ('a, 'b) t -> bool

val mem_bound : int -> ('a, 'b) t -> bool

(** [at_level ~lvl asmp] removes bound variables below [lvl] and subtracts [lvl] from the other ones. *)
val at_level : lvl:int -> ('a, 'b) t -> ('a, 'b) t

(** [shift ~lvl k asmp] shifts bound variables above [lvl] by [k]. *)
val shift : lvl:int -> int -> ('a, 'b) t -> ('a, 'b) t

val singleton_bound : int -> ('a, 'b) t

val add_free : Name.atom -> 'a -> ('a, 'b) t -> ('a, 'b) t

val add_bound : int -> ('a, 'b) t -> ('a, 'b) t

val union : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t

(** [instantiate asmp0 ~lvl:k asmp] replaces bound variable [k] with the assumptions [asmp0] in [asmp]. *)
val instantiate : ('a, 'b) t -> lvl:int -> ('a, 'b) t -> ('a, 'b) t

(** [fully_instantiate asmps ~lvl:k asmp] replaces bound variables in [asmp] with assumptions [asmps]. *)
val fully_instantiate : ('a, 'b) t list -> lvl:int -> ('a, 'b) t -> ('a, 'b) t

(** [abstract x ~lvl:k l] replaces the free variable [x] by the bound variable [k]. *)
val abstract : Name.atom -> lvl:int -> ('a, 'b) t -> ('a, 'b) t

module Json :
sig

  val assumptions : ('a, 'b) t -> Json.t

end
