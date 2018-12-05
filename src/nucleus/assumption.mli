(** Sets of assumptions *)
module BoundSet : Set.S with type elt = int

(** A pair of sets, corresponding to free and bound assumptions *)
type ('a, 'b, 'c, 'd, 'e) t

val empty : ('a, 'b, 'c, 'd, 'e) t

val is_empty : ('a, 'b, 'c, 'd, 'e) t -> bool

val unpack : ('a, 'b, 'c, 'd, 'e) t
  -> 'a Name.AtomMap.t
     * 'b Name.MetaMap.t
     * 'c Name.MetaMap.t
     * 'd Name.MetaMap.t
     * 'e Name.MetaMap.t
     * BoundSet.t

val mem_atom : Name.atom -> ('a, 'b, 'c, 'd, 'e) t -> bool

val mem_bound : int -> ('a, 'b, 'c, 'd, 'e) t -> bool

(** [at_level ~lvl asmp] removes bound variables below [lvl] and subtracts [lvl] from the other ones. *)
val at_level : lvl:int -> ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t

(** [shift ~lvl k asmp] shifts bound variables above [lvl] by [k]. *)
val shift : lvl:int -> int -> ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t

val singleton_bound : int -> ('a, 'b, 'c, 'd, 'e) t

val add_free : Name.atom -> 'a -> ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t

val add_is_type_meta : Name.meta -> 'b -> ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t
val add_is_term_meta : Name.meta -> 'c -> ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t
val add_eq_type_meta : Name.meta -> 'd -> ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t
val add_eq_term_meta : Name.meta -> 'e -> ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t

val add_bound : int -> ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t

val union : ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t -> ('a, 'b, 'c, 'd, 'e) t

(** [instantiate asmp0 ~lvl:k asmp] replaces bound variable [k] with the assumptions [asmp0] in [asmp]. *)
val instantiate : ('a, 'b, 'c, 'd, 'e) t -> lvl:int -> ('a, 'b, 'c, 'd, 'e) t
  -> ('a, 'b, 'c, 'd, 'e) t

(** [fully_instantiate asmps ~lvl:k asmp] replaces bound variables in [asmp] with assumptions [asmps]. *)
val fully_instantiate : ('a, 'b, 'c, 'd, 'e) t list -> lvl:int
  -> ('a, 'b, 'c, 'd, 'e) t
  -> ('a, 'b, 'c, 'd, 'e) t

(** [abstract x ~lvl:k l] replaces the free variable [x] by the bound variable [k]. *)
val abstract : Name.atom -> lvl:int -> ('a, 'b, 'c, 'd, 'e) t
  -> ('a, 'b, 'c, 'd, 'e) t

module Json :
sig

  val assumptions : ('a, 'b, 'c, 'd, 'e) t -> Json.t

end
