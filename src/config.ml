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

let debruijn = ref false

let annotate = ref false

let print_dependencies = ref false

let max_boxes = ref 42

let print_subscripts = ref true
