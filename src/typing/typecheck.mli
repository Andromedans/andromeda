(** [toplevel env c] checks that toplevel command [c] is well typed and updates the environment accordingly. *)
val toplevel : Tyenv.t -> Dsyntax.toplevel -> Tyenv.t * Rsyntax.toplevel

(** Typecheck commands that were loaded from a file *)
val toplevels : Tyenv.t -> Dsyntax.toplevel list -> Tyenv.t * Rsyntax.toplevel list

(** The initial typing context with built-in definitions *)
val initial_context : Tyenv.t

(** The commands which need to be executed in the empty runtime environment to obtain a runtime environment counter-part to
    [initial_context] *)
val initial_commands : Rsyntax.toplevel list

module Builtin :
sig

  val equal_term : Ident.t * (Mlty.ty list * Mlty.ty)
  val equal_type : Ident.t * (Mlty.ty list * Mlty.ty)
  val coerce : Ident.t * (Mlty.ty list * Mlty.ty)

end
