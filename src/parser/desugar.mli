(** Conversion from sugared to desugared input syntax *)

(** [toplevel primitive bound c] desugars a toplevel command [c] with a
    list of primitives and their arities, and a list of bound variables
    that are converted to de Bruijn indiced. *)
val toplevel : Boundinfo.ctx -> Input.toplevel -> Syntax.toplevel
