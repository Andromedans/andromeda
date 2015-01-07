(** Conversion from the input syntax to the abstract syntax. *)

val computation : Input.comp -> Syntax.comp

val toplevel : Common.name list -> Input.toplevel -> Syntax.toplevel
