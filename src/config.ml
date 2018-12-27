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

let json_location = ref false

let columns = ref (Format.get_margin ())
