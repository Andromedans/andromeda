(** Names of free variables *)
type name = string

(** Bound variables *)
type bound = int

(** Comparison of free variables *)
val eqname : name -> name -> bool
