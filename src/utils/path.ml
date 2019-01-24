type index = Index of Name.t * int

type level = Level of Name.t * int

type t =
  | Direct of level
  | Module of t * level

type ml_constructor = t * level

let print_level (Level (x, _)) ppf = Name.print x ppf

let rec print p ppf =
  match p with
  | Direct x -> print_level x ppf
  | Module (pth, x) -> Format.fprintf ppf "%t.%t" (print pth) (print_level x)
