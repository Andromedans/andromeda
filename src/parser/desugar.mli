(** Conversion from the input syntax to the abstract syntax. *)

val computation : Input.comp -> Syntax.comp

val toplevel : Name.t list -> Input.toplevel -> Syntax.toplevel
