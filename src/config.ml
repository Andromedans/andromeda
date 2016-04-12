(** Configuration parameters *)

type prelude =
  | PreludeNone
  | PreludeDefault
  | PreludeFile of string

let prelude_file = ref PreludeDefault

let interactive_shell = ref true

let wrapper = ref (Some ["rlwrap"; "ledit"])

let verbosity = ref 2

let ascii = ref false

let max_boxes = ref 42

let global_atom_printer = ref false

let columns = ref (Format.get_margin ())

type appty_guess =
  | NoGuess
  | GuessJdg
  | GuessArrow

let appty_guess = ref GuessArrow

