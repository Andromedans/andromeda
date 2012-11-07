(* Contexts *)
let lookup = List.assoc

let index x ctx =
  let rec index k = function
    | [] -> raise Not_found
    | y :: ys -> if x = y then k else index (k+1) ys
  in
    index 0 ctx

let lookup_ty x ctx = fst (lookup x ctx)

let lookup_value x ctx = snd (lookup x ctx)

let extend x t ?value ctx = (x, (t, value)) :: ctx


