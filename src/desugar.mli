(** Conversion from the input syntax to the abstract syntax. *)

val computation : Input.comp -> Syntax.comp

val toplevel : Input.toplevel -> Syntax.toplevel
