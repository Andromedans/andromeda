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

(** Given a variable [x] and a list of variables [xs], find a
    variant of [x] which does not appear in [xs]. *)
let find_name x xs =
  (** Split a string into base and numerical postfix, e.g.,
      ["x42"] is split into [("x", 42)]. *)
  let split s =
    let n = String.length s in
    let i = ref (n - 1) in
      while !i >= 0 && '0' <= s.[!i] && s.[!i] <= '9' do decr i done ;
      if !i < 0 || !i = n - 1
      then (s, None)
      else
        let k = int_of_string (String.sub s (!i+1) (n - !i - 1)) in
          (String.sub s 0 (!i+1), Some k)
  in

  if not (List.mem (String x) xs)
  then String x
  else
    let (y, k) = split x in
    let k = ref (match k with Some k -> k | None -> 0) in
      while List.mem (String (y ^ string_of_int !k)) xs do incr k done ;
      String (y ^ string_of_int !k)

let refresh xs = function
  | Anonymous -> Anonymous
  | String y
  | Gensym (y, _) -> find_name y xs

let eq (x : t) (y : t) = (x = y)

let index_of x ys =
  let rec fold k = function
    | [] -> None
    | y :: ys -> if eq x y then Some k else fold (k + 1) ys
  in
    fold 0 ys

let print x ppf = Print.print ~at_level:0 ppf "%s" (to_string x)
