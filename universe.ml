type uvar = UVar of int

(** A universe level is represented as [max(k, u1 + k1, ..., un + kn)] where [u1, ..., un]
    are distinct existential variables, and [k, k1, ..., kn] are natural numbers. *)
type universe = int * (uvar * int) list

let add (k, lst) m = (k + m, List.map (fun (u, k) -> (u, k + m)) lst)

let succ u = add u 1

let umax (k, us) (m, vs) =
  let rec join lst (u, m) =
    match lst with
      | [] -> [(u, m)]
      | (v, n) :: lst -> if v = u then (v, max m n) :: lst else (v, n) :: join lst (u, m)
  in
   (max k m, List.fold_left join us vs)

(** Generate a fresh universe variable. *)
let fresh_uvar =
  let k = ref 0 in
    fun () -> (incr k ; UVar !k)

let fresh_universe () = (0, [(fresh_uvar (), 0)])

let subst_universe s (k, lst) =
  List.fold_left
    (fun us (u, n) -> umax us (add (try List.assoc u s with Not_found -> (0, [(u, 0)])) n))
    (k, []) lst
