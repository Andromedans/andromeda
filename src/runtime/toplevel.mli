(** Evaluation of interactive commands and files *)

(** Contains the desugaring context, the typing context and the runtime environment synchronized with each other. *)
type state

(** The type of errors that may be reported to the toplevel. *)
type error

exception Error of error

val print_error : state -> error -> Format.formatter -> unit

(** Run a command from the interactive input. *)
val exec_interactive : state -> state

(** Run commands from a file *)
val use_file : quiet:bool -> string -> state -> state

(** Load a file as a module *)
val load_ml_module : fn:string -> quiet:bool -> state -> state

(** The initial toplevel environment *)
val initial_environment : state
