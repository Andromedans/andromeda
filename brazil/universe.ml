type t =
  | Fibered of int
  | NonFibered of int

let of_string s =
  let n = String.length s in
  if n = 0 then None
  else
    try
      if s.[0] = 'f' || s.[0] = 'F' then
        let u = int_of_string (String.sub s 1 (n - 1)) in
          Some (Fibered u)
      else
        let u = int_of_string s in
          Some (NonFibered u)
    with Failure _ -> None

let to_string = function
  | Fibered k -> "fib" ^ string_of_int k
  | NonFibered k -> string_of_int k

let zero = Fibered 0
  
let is_fibered = function
  | Fibered _ -> true
  | NonFibered _ -> false

let leq u v =
  match u, v with
    | (Fibered k | NonFibered k), (Fibered m | NonFibered m) ->
      k < m || (k = m && is_fibered u)

let succ = function
  | Fibered k -> Fibered (k + 1)
  | NonFibered k -> Fibered (k + 1)

let max u v =
  match u, v with
    | Fibered k, Fibered m -> Fibered (Pervasives.max k m)
    | NonFibered k, Fibered m
    | Fibered k, NonFibered m
    | NonFibered k, NonFibered m ->
      NonFibered (Pervasives.max k m)

