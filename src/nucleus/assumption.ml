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

let mem_bound k s = BoundSet.mem k s.bound

let shift lvl s =
  { s with
    bound = BoundSet.fold
              (fun k s -> if k < lvl then s else BoundSet.add (k - lvl) s)
              s.bound BoundSet.empty }

let singleton_free x =
  {free = AtomSet.singleton x; bound = BoundSet.empty}

let singleton_bound k =
  {free = AtomSet.empty; bound = BoundSet.singleton k}

let add_atoms a {free;bound} =
  {free = AtomSet.union free a; bound}

let add_free a asmp = {asmp with free = AtomSet.add a asmp.free}

let add_bound k asmp = {asmp with bound = BoundSet.add k asmp.bound}

let union a1 a2 =
  {free=AtomSet.union a1.free a2.free; bound=BoundSet.union a1.bound a2.bound}

let instantiate l0 ~lvl asmp =
  if BoundSet.mem lvl asmp.bound
  then
    { free = AtomSet.union asmp.free l0.free
    ; bound = BoundSet.union (BoundSet.remove lvl asmp.bound) l0.bound }
    (* XXX think whether the above is correct, in particular:
       1. could tehre be bound variables larger than lvl in asmp.bound, and if so, should they be shifted?
       2. do we need to reindex the bound variables of l0 or some such? *)
  else
    asmp

let abstract x ~lvl abstr =
  if AtomSet.mem x abstr.free
  then
    { free = AtomSet.remove x abstr.free
    ; bound = BoundSet.add lvl abstr.bound
    }
  else
    abstr

let bind1 {free;bound} =
  let bound = BoundSet.fold (fun n bound ->
      if n = 0
      then bound
      else BoundSet.add (n - 1) bound)
    bound BoundSet.empty
  in
  {free;bound}

let as_atom_set {free;bound;} =
  assert (BoundSet.is_empty bound) ;
  free

let equal {free=free1;bound=bound1} {free=free2;bound=bound2} =
  AtomSet.equal free1 free2 && BoundSet.equal bound1 bound2

module Json =
struct

  let assumptions {free; bound} =
    let free =
      if AtomSet.is_empty free
      then []
      else [("free", Name.Json.atomset free)]
    and bound =
      if BoundSet.is_empty bound
      then []
      else [("bound", Json.List (List.map (fun k -> Json.Int k) (BoundSet.elements bound)))]
    in
      Json.record (free @ bound)

end
