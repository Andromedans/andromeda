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

let compare_level (Level (_, i)) (Level (_, j)) =
  if i < j then -1
  else if j < i then 1
  else 0

let compare_path pth1 pth2 =
  match pth1, pth2 with
  | Direct _, Module _ -> -1
  | Module _, Direct _ -> 1
  | Direct x1, Direct x2 -> compare_level x1 x2
  | Module (pth1, x1), Module (pth2, x2) ->
     let c = compare_level x1 x2 in
     if c = 0 then compare pth1 pth2 else c


module PathMap = Map.Make(
                     struct
                       type nonrec t = t
                       let compare = compare_path
                     end)

type 'a map = 'a PathMap.t

let empty = PathMap.empty

let add = PathMap.add

let find = PathMap.find
