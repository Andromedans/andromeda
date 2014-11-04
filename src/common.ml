type name = string

(** Bound variables are represented by de Bruijn indices *)
type bound = int

let eqname (s : name) (t : name) = (s = t)
