(** Evaluation of top level commands *)

(** Contains the desugaring context, the typing context and the runtime environment synchronized with each other. *)
type state

(** The type of errors that may be reported to the toplevel. *)
type error =
  | RuntimeError of Runtime.error * Tt.print_env
  | ContextError of Context.error * Tt.print_env

exception Error of error Location.located

val print_error: error -> Format.formatter -> unit

(** [exec_cmd d] executes toplevel command [c].
    It prints the result if in interactive mode.
    The environment is passed through a state monad. *)
val exec_cmd : quiet:bool -> Input.toplevel -> state -> state

(** Load directives from the given file. *)
val use_file : fn:string -> quiet:bool -> state -> state

val initial : state

