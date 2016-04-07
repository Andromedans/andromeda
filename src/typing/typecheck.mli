
(** [toplevel env c] checks that toplevel command [c] is well typed and updates the environment accordingly. *)
val toplevel : Tyenv.t -> Syntax.toplevel -> Tyenv.t

