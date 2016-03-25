type t =
  | SysError of string

let print err ppf = match err with
  | SysError s -> Format.fprintf ppf "System error: %s" s

exception Error of t Location.located

let raise ~loc err = Pervasives.raise (Error (Location.locate err loc))

