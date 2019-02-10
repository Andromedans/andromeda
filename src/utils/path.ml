type index = Index of Name.t * int

type level = Level of Name.t * int

type t =
  | Direct of level
  | Module of t * level

type ml_constructor = t * level

let print_level ?parentheses (Level (x, _)) ppf = Name.print ?parentheses x ppf

let rec print ~parentheses p ppf =
  match p with
  | Direct x -> print_level ~parentheses x ppf
  | Module (pth, x) -> Format.fprintf ppf "%t.%t" (print ~parentheses:true pth) (print_level ~parentheses:true x)

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

let equal pth1 pth2 = (0 = compare_path pth1 pth2)

module PathMap = Map.Make(
                     struct
                       type nonrec t = t
                       let compare = compare_path
                     end)

type 'a map = 'a PathMap.t

let empty = PathMap.empty

let add = PathMap.add

let find = PathMap.find

module Json =
struct
  let level (Level (name, _)) = Name.Json.name name

  let path pth =
    let rec collect acc = function
      | Direct lvl -> lvl :: acc
      | Module (mdl, lvl) -> collect (lvl :: acc) mdl
    in
    let lst = collect [] pth in
    Json.tuple (List.map level lst)
end
