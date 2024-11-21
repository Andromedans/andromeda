(** Configuration parameters *)

type prelude =
  | PreludeNone
  | PreludeDefault of string
  | PreludeFile of string

let prelude_file = ref (PreludeDefault "prelude.m31")

type stdlib =
  | StdlibNone
  | StdlibDefault of string
  | StdlibDirectory of string

let stdlib_directory = ref (StdlibDefault "stdlib")

let interactive_shell = ref true

let wrapper = ref (Some ["rlwrap"; "ledit"])

let verbosity = ref 2

let ascii = ref false

let max_boxes = ref 42

let json_location = ref false

let columns = ref (Format.get_margin ())

let require_dirs = ref []
