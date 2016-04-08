(** Configuration parameters *)

(** Possible locations of prelude file *)
type prelude =
  | PreludeNone              (* do not use a prelude, turned on by the --no-prelude *)
  (* look in the default location, which is the $(LIB_DIR) or next to the executable *)
  | PreludeDefault
  | PreludeFile of string    (* look for prelude in a specific location *)

(** Location of the prelude file *)
val prelude_file : prelude ref

(** Should the interactive shell be run? *)
val interactive_shell : bool ref

(** The command-line wrappers that we look for. *)
val wrapper : string list option ref

(** Select which messages should be printed:
    - 0 no messages
    - 1 only errors
    - 2 errors and warnings
    - 3 errors, warnings, and debug messages *)
val verbosity : int ref

(** Print using ASCII format rather than UTF8 *)
val ascii : bool ref

(** How deeply to print output *)
val max_boxes : int ref

(** The maximum number of characters that will be printed on one line *)
val columns : int ref

(** Should atoms be printed with freshness subscripts? *)
val global_atom_printer : bool ref

