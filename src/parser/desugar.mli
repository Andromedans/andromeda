(** Conversion from sugared to desugared input syntax *)

(** [toplevel xs c] desugars a toplevel command [c] with a list [xs] of names
    of bound variables (needed for conversion to de Bruijn indices) *)
val toplevel : Name.t list -> Input.toplevel -> Syntax.toplevel
