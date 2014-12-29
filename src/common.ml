type name =
  | Anonymous
  | Gensym of int
  | String of string

(** Bound variables are represented by de Bruijn indices *)
type bound = int

let anonymous = Anonymous

let to_name x = String x

let to_string = function
  | Anonymous -> "_"
  | Gensym n -> "_" ^ string_of_int n
  | String s -> s

let fresh =
  let k = ref (-1)
  in fun () -> (incr k ; Gensym (!k))

let eqname (s : name) (t : name) = (s = t)

let rec index_of shift x = function
  | [] -> None
  | y :: ys -> if eqname x y then Some shift else index_of (shift + 1) x ys
