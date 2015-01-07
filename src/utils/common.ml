type name =
  | Anonymous
  | Gensym of string * int
  | String of string

(** Bound variables are represented by de Bruijn indices *)
type bound = int

let anonymous = Anonymous

let to_name x = String x

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

let eqname (s : name) (t : name) = (s = t)

let rec index_of shift x = function
  | [] -> None
  | y :: ys -> if eqname x y then Some shift else index_of (shift + 1) x ys
