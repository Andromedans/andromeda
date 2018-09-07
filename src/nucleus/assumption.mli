(** Sets of assumptions *)
module BoundSet : Set.S with type elt = int

(** A pair of sets, corresponding to free and bound assumptions *)
type t

val empty : t

val is_empty : t -> bool

val mem_atom : Name.atom -> t -> bool

val mem_bound : int -> t -> bool

(** [shift lvl asmp] removes bound variables below [lvl] and subtracts [lvl] from the other ones. *)
val shift : int -> t -> t

val singleton_free : Name.atom -> t

val singleton_bound : int -> t

val add_atoms : Name.AtomSet.t -> t -> t

val add_free : Name.atom -> t -> t

val add_bound : int -> t -> t

val union : t -> t -> t

(** [instantiate a0 k a] replaces bound variable [k] with the assumptions of [a0] *)
val instantiate : t -> lvl:int -> t -> t

(** [abstract x k l] replaces the free variable [x] by the bound variables [k]. *)
val abstract : Name.atom -> lvl:int -> t -> t

(** If [hyps] are the assumptions on a term, [bind hyps] are the assumptions after putting the term under a binder. *)
val bind1 : t -> t

(** If [a] has no bound assumptions, [as_atom_set a] returns the set of free assumptions. *)
val as_atom_set : t -> Name.AtomSet.t

val equal : t -> t -> bool

module Json :
sig

  val assumptions : t -> Json.t

end
