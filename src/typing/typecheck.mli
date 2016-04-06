
(** [toplevel env c] checks that toplevel command [c] is well typed and updates the environment accordingly. *)
val toplevel : quiet:bool -> Tyenv.TopEnv.t -> Syntax.toplevel -> Tyenv.TopEnv.t

