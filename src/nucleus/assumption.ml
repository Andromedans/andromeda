module BoundSet = Set.Make (struct
                    type t = int
                    let compare = compare
                  end)

module AtomMap = Name.AtomMap

module MetaMap = Name.MetaMap

type ('a, 'b) t = { free : 'a AtomMap.t; meta : 'b MetaMap.t ; bound : BoundSet.t }

let empty = { free = AtomMap.empty; meta = MetaMap.empty; bound = BoundSet.empty }

let is_empty {free;meta;bound} =
  AtomMap.is_empty free && MetaMap.is_empty meta && BoundSet.is_empty bound

let unpack {free; meta; bound} = free, meta, bound

let mem_atom x s = AtomMap.mem x s.free

let mem_bound k s = BoundSet.mem k s.bound

let at_level ~lvl s =
  { s with
    bound = BoundSet.fold
              (fun k s -> if k < lvl then s else BoundSet.add (k - lvl) s)
              s.bound BoundSet.empty }

let shift ~lvl k s =
  { s with
    bound =
      BoundSet.fold
        (fun j s -> BoundSet.add (if j < lvl then j else j + k) s)
        s.bound
        BoundSet.empty }

let singleton_bound k = {empty with bound = BoundSet.singleton k}

let add_free x t asmp = {asmp with free = AtomMap.add x t asmp.free}

let add_meta x t asmp = {asmp with meta = MetaMap.add x t asmp.meta}

let add_bound k asmp = {asmp with bound = BoundSet.add k asmp.bound}

let singleton_meta x t = add_meta x t empty

let union a1 a2 =
  let f = (fun vtype print a t1 t2 ->
      (if not (t1 == t2)
      then Print.error "XXX %s variable %t occurs at physically different types@." vtype (print a)
      else ()) ;
      assert (t1 = t2) ; Some t1) in
  let f_free = (f "free" (Name.print_atom ~parentheses:false ~printer:(Name.atom_printer ())))
  and f_meta = (f "meta" (Name.print_meta ~parentheses:false ~printer:(Name.meta_printer ()))) in
  { free = AtomMap.union f_free a1.free a2.free
  ; meta = MetaMap.union f_meta a1.meta a2.meta
  ; bound = BoundSet.union a1.bound a2.bound
  }

let instantiate asmp0 ~lvl asmp =
  match BoundSet.mem lvl asmp.bound with
  | false -> asmp
  | true ->
     let bound0 = BoundSet.map (fun k -> lvl + k) asmp0.bound
     and bound = BoundSet.remove lvl asmp.bound
     in
     let asmp0 = {asmp0 with bound = bound0}
     and asmp = {asmp with bound} in
     union asmp asmp0

let fully_instantiate asmps ~lvl asmp =
  let rec fold asmp = function
    | [] -> asmp
    | asmp0 :: asmps ->
       let asmp = instantiate asmp0 ~lvl asmp
       in fold asmp asmps
  in
  fold asmp asmps

let abstract x ~lvl abstr =
  if AtomMap.mem x abstr.free
  then
    { free = AtomMap.remove x abstr.free
    ; meta = abstr.meta
    ; bound = BoundSet.add lvl abstr.bound
    }
  else
    abstr

module Json =
struct

  let assumptions {free; meta; bound} =
    let free =
      if AtomMap.is_empty free
      then []
      else [("free", Name.Json.atommap free)]
    and meta =
      if MetaMap.is_empty meta
      then []
      else [("meta", Name.Json.metamap meta)]
    and bound =
      if BoundSet.is_empty bound
      then []
      else [("bound", Json.List (List.map (fun k -> Json.Int k) (BoundSet.elements bound)))]
    in
      Json.record (free @ meta @ bound)

end
