(** [toplevel env c] checks that toplevel command [c] is well typed and updates the environment accordingly. *)
val toplevel : Tyenv.t -> Dsyntax.toplevel -> Tyenv.t * Rsyntax.toplevel
