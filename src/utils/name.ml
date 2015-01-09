type t =
  | Anonymous
  | Gensym of string * int
  | String of string

let anonymous = Anonymous

let of_string x = String x

let to_string = function
  | Anonymous -> "_"
  | Gensym (x, k)  -> "gensym_" ^ x ^ "_" ^ string_of_int k
  | String s -> s

let fresh =
  let k = ref (-1)
  in fun x ->
     incr k ;
     if !k < 0 then Error.impossible "you will not get a beer if you do not report this error" ;
     let y = 
       match x with
       | Anonymous -> "_"
       | String x -> x
       | Gensym (x, _) -> x
     in 
       Gensym (y, !k)

let eq (x : t) (y : t) = (x = y)

let rec index_of shift x = function
  | [] -> None
  | y :: ys -> if eq x y then Some shift else index_of (shift + 1) x ys

let rec rindex_of shift x xs = index_of shift x (List.rev xs)

let print x ppf = Print.print ~at_level:0 ppf "%s" (to_string x)
