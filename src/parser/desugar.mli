(** Conversion from sugared to desugared input syntax *)

module Bound : sig type t val empty : t end

(** [toplevel primitive bound c] desugars a toplevel command [c] with a
    list of primitives and their arities, and a list of bound variables
    that are converted to de Bruijn indiced. *)
val toplevel : Bound.t -> Input.toplevel -> Bound.t * Syntax.toplevel list
