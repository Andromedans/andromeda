(** Sets of assumptions *)
module BoundSet : Set.S with type elt = int

(** A pair of sets, corresponding to free and bound assumptions *)
type 'a t

val empty : 'a t

val is_empty : 'a t -> bool

val mem_atom : Name.atom -> 'a t -> bool

val mem_bound : int -> 'a t -> bool

(** [shift lvl asmp] removes bound variables below [lvl] and subtracts [lvl] from the other ones. *)
val shift : lvl:int -> 'a t -> 'a t

val singleton_free : Name.atom -> 'a -> 'a t

val singleton_bound : int -> 'a t

val add_free : Name.atom -> 'a -> 'a t -> 'a t

val add_bound : int -> 'a t -> 'a t

val union : 'a t -> 'a t -> 'a t

(** [instantiate a0 k a] replaces bound variable [k] with the assumptions of [a0] *)
val instantiate : 'a t -> lvl:int -> 'a t -> 'a t

(** [abstract x k l] replaces the free variable [x] by the bound variables [k]. *)
val abstract : Name.atom -> lvl:int -> 'a t -> 'a t

(** If [hyps] are the assumptions on a term, [bind hyps] are the assumptions after putting the term under a binder. *)
val bind1 : 'a t -> 'a t

val equal : 'a t -> 'a t -> bool

module Json :
sig

  val assumptions : 'a t -> Json.t

end
