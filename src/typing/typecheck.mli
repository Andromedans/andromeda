
(** [toplevel env c] checks that toplevel command [c] is well typed and updates the environment accordingly. *)
val toplevel : quiet:bool -> Tyenv.t -> Syntax.toplevel -> Tyenv.t

