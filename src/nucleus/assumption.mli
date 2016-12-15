(** Sets of assumptions *)
module BoundSet : Set.S with type elt = int

type t

val empty : t

val is_empty : t -> bool

val mem_atom : Name.atom -> t -> bool

val singleton : Name.atom -> t

val of_atoms : Name.AtomSet.t -> t

val add_atoms : Name.AtomSet.t -> t -> t

val union : t -> t -> t

(** [instantiate l lvl a] where [l] is [a0 ... an]
    replaces bound variable [lvl+k] by the assumptions [ak] for k<=n,
    by lvl+k-n for k>n and leaves k<lvl unchanged*)
val instantiate : t list -> int -> t -> t

(** [abstract a lvl l] where [l] is [x0 ... xn]
    replaces the free variables [x0 ... xn] by the bound variables [lvl ... lvl+n] respectively. *)
val abstract : Name.atom list -> int -> t -> t

(** If [hyps] are the assumptions on a term, [bind hyps] are the assumptions after putting the term under a binder. *)
val bind1 : t -> t

(** If [a] has no bound assumptions, [as_atom_set a] returns the set of free assumptions. *)
val as_atom_set : loc:Location.t -> t -> Name.AtomSet.t

val equal : t -> t -> bool

module Json :
sig

  val assumptions : t -> Json.t

end
