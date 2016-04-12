
(** [toplevel env c] checks that toplevel command [c] is well typed and updates the environment accordingly. *)
val toplevel : Tyenv.t -> Syntax.ml_schema option Syntax.toplevel -> Tyenv.t * Mlty.ty_schema Syntax.toplevel

