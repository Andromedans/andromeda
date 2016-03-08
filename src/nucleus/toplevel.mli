(** Evaluation of top level commands *)

(** Parser wrapper that reads extra lines on demand. *)
val parse : ('a -> 'b -> 'c) -> 'a -> 'b -> 'c

(** Load directives from the given file. *)
val use_file : string * int option * bool * bool -> unit Runtime.toplevel

(** [exec_cmd d] executes toplevel command [c].
    It prints the result if in interactive mode.
    The environment is passed through a state monad. *)
val exec_cmd : string -> bool -> Input.toplevel -> unit Runtime.toplevel

