module BoundSet = Set.Make (struct
                    type t = int
                    let compare = compare
                  end)

module AtomSet = Name.AtomSet

type t = { free : AtomSet.t; bound : BoundSet.t }

let empty = {free = AtomSet.empty; bound = BoundSet.empty; }

let is_empty {free;bound} =
  AtomSet.is_empty free && BoundSet.is_empty bound

let print xs {free;bound} ppf =
  Format.fprintf ppf "%t@ ;@ %t"
              (Print.sequence Name.print_atom "," (AtomSet.elements free))
              (Print.sequence (Name.print_debruijn xs) "," (BoundSet.elements bound))

let singleton x =
  let free = AtomSet.add x AtomSet.empty in
  {free;bound=BoundSet.empty;}

let add_atoms a {free;bound;} =
  {free=AtomSet.union free a;bound;}

let union a1 a2 =
  {free=AtomSet.union a1.free a2.free; bound=BoundSet.union a1.bound a2.bound}

let instantiate l lvl {free;bound;} =
  let acc, n = List.fold_left (fun (acc,n) an ->
      if BoundSet.mem (n+lvl) bound
      then
        let free = AtomSet.union acc.free an.free
        and bound = BoundSet.union acc.bound an.bound in
        ({free;bound;},n+1)
      else (acc,n+1))
    (empty,0) l
  in
  let bound = BoundSet.fold (fun k bound ->
      if k < lvl
      then BoundSet.add k bound
      else if k < lvl+n
      then bound
      else BoundSet.add (k-n) bound)
    bound BoundSet.empty
  in
  let free = AtomSet.union free acc.free
  and bound = BoundSet.union bound acc.bound in
  {free;bound;}

let abstract l lvl a =
  let acc,_ = List.fold_left (fun (acc,n) xn ->
      if AtomSet.mem xn acc.free
      then
        let free = AtomSet.remove xn acc.free
        and bound = BoundSet.add (lvl+n) acc.bound in
        ({free;bound;},n+1)
      else (acc,n+1))
    (a,0) l
  in
  acc

let bind k {free;bound} =
  let bound = BoundSet.fold (fun n bound ->
      if n < k
      then bound
      else BoundSet.add (n-k) bound)
    bound BoundSet.empty
  in
  {free;bound}

let as_atom_set ~loc {free;bound;} =
  if BoundSet.is_empty bound
  then free
  else Error.impossible ~loc "reducing assumptions to free assumptions not allowed when there are bound assumptions"

