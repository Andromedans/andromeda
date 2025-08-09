(** Configuration parameters *)

let stdlibDir : string option =
  match SharedFiles.Sites.stdlib with
  | [] -> None
  | d :: _ -> Some d

let prelude_file =
  ref (match stdlibDir with
       | None -> None
       | Some dir -> Some (Filename.concat dir "prelude.m31"))

let stdlib_directory =
  ref (match stdlibDir with
       | None -> None
       | Some dir -> Some dir)

let interactive_shell = ref true

let wrapper = ref (Some ["rlwrap"; "ledit"])

let verbosity = ref 2

let ascii = ref false

let max_boxes = ref 42

let json_location = ref false

let columns = ref (Format.get_margin ())

let require_dirs = ref []
