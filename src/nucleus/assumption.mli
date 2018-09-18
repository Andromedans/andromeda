(** Sets of assumptions *)
module BoundSet : Set.S with type elt = int

(** A pair of sets, corresponding to free and bound assumptions *)
type 'a t

val empty : 'a t

val is_empty : 'a t -> bool

val mem_atom : Name.atom -> 'a t -> bool

val mem_bound : int -> 'a t -> bool

(** [at_level ~lvl asmp] removes bound variables below [lvl] and subtracts [lvl] from the other ones. *)
val at_level : lvl:int -> 'a t -> 'a t

(** [shift ~lvl k asmp] shifts bound variables above [lvl] by [k]. *)
val shift : lvl:int -> int -> 'a t -> 'a t

val singleton_free : Name.atom -> 'a -> 'a t

val singleton_bound : int -> 'a t

val add_free : Name.atom -> 'a -> 'a t -> 'a t

val add_bound : int -> 'a t -> 'a t

val union : 'a t -> 'a t -> 'a t

(** [instantiate asmp0 ~lvl:k asmp] replaces bound variable [k] with the assumptions [asmp0] in [asmp]. *)
val instantiate : 'a t -> lvl:int -> 'a t -> 'a t

(** [fully_instantiate asmps ~lvl:k asmp] replaces bound variables in [asmp] with assumptions [asmps]. *)
val fully_instantiate : 'a t list -> lvl:int -> 'a t -> 'a t

(** [abstract x k l] replaces the free variable [x] by the bound variables [k]. *)
val abstract : Name.atom -> lvl:int -> 'a t -> 'a t

(** If [hyps] are the assumptions on a term, [bind hyps] are the assumptions after putting the term under a binder. *)
val bind1 : 'a t -> 'a t

val equal : 'a t -> 'a t -> bool

module Json :
sig

  val assumptions : 'a t -> Json.t

end
