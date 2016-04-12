module BoundSet = Set.Make (struct
                    type t = int
                    let compare = compare
                  end)

module AtomSet = Name.AtomSet

type t = { free : AtomSet.t; bound : BoundSet.t }

let empty = {free = AtomSet.empty; bound = BoundSet.empty; }

let is_empty {free;bound} =
  AtomSet.is_empty free && BoundSet.is_empty bound

let mem_atom x s = AtomSet.mem x s.free

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

let bind1 {free;bound} =
  let bound = BoundSet.fold (fun n bound ->
      if n = 0
      then bound
      else BoundSet.add (n - 1) bound)
    bound BoundSet.empty
  in
  {free;bound}

let as_atom_set ~loc {free;bound;} =
  assert (BoundSet.is_empty bound) ;
  free

let equal {free=free1;bound=bound1} {free=free2;bound=bound2} =
  AtomSet.equal free1 free2 && BoundSet.equal bound1 bound2

module Json =
struct

  let assumptions {free; bound} =
    let bound = List.map (fun k -> Json.Int k) (BoundSet.elements bound) in
    Json.record "assumptions" ["free", Name.Json.atomset free;
                               "bound", Json.List bound]

end
