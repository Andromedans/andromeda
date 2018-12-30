(** Evaluation of interactive commands and files *)

(** Contains the desugaring context, the typing context and the runtime environment synchronized with each other. *)
type state

(** The type of errors that may be reported to the toplevel. *)
type error

exception Error of error

val print_error : state -> error -> Format.formatter -> unit

(** Run a command from the interactive input. *)
val exec_interactive : state -> state

(** Run commands from the given file. *)
val use_file : fn:string -> quiet:bool -> state -> state

val initial : state
