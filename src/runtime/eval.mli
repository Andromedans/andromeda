(** Evaluation of computations *)

type error

exception Error of error Location.located

val print_error : error -> Format.formatter -> unit

val toplevel : quiet:bool -> Syntax.toplevel -> unit Runtime.toplevel

