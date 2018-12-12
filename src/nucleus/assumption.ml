open Jdg_typedefs

let empty =
  let meta = MetaMap.empty in
  { free = AtomMap.empty
  ; is_type_meta = meta
  ; is_term_meta = meta
  ; eq_type_meta = meta
  ; eq_term_meta = meta
  ; bound = BoundSet.empty }

let is_empty { free ; is_type_meta ; is_term_meta ; eq_type_meta ; eq_term_meta ; bound } =
  AtomMap.is_empty free
  && MetaMap.is_empty is_type_meta
  && MetaMap.is_empty is_term_meta
  && MetaMap.is_empty eq_type_meta
  && MetaMap.is_empty eq_term_meta
  && BoundSet.is_empty bound

let unpack { free ; is_type_meta ; is_term_meta ; eq_type_meta ; eq_term_meta ; bound } =
  free, is_type_meta, is_term_meta, eq_type_meta, eq_term_meta, bound

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

let singleton_bound k = { empty with bound = BoundSet.singleton k }

let add_free x t asmp = { asmp with free = AtomMap.add x t asmp.free }

let add_is_type_meta x t asmp = { asmp with is_type_meta = MetaMap.add x t asmp.is_type_meta }
let add_is_term_meta x t asmp = { asmp with is_term_meta = MetaMap.add x t asmp.is_term_meta }
let add_eq_type_meta x t asmp = { asmp with eq_type_meta = MetaMap.add x t asmp.eq_type_meta }
let add_eq_term_meta x t asmp = { asmp with eq_term_meta = MetaMap.add x t asmp.eq_term_meta }

let add_bound k asmp = { asmp with bound = BoundSet.add k asmp.bound }

let union a1 a2 =
  let f = (fun vtype print a t1 t2 ->
      (if not (t1 == t2)
      then
        (Print.error "XXX %s variable %t occurs at physically different types@." vtype (print a)
         ; assert false )
      else ()) ;
      Some t1) in
  let f_free = (f "free" (Name.print_atom ~parentheses:false ~printer:(Name.atom_printer ())))
  and p_meta = Name.print_meta ~parentheses:false ~printer:(Name.meta_printer ())
  in
  { free = AtomMap.union f_free a1.free a2.free
  ; is_type_meta = MetaMap.union (f "is_type_meta" p_meta) a1.is_type_meta a2.is_type_meta
  ; is_term_meta = MetaMap.union (f "is_term_meta" p_meta) a1.is_term_meta a2.is_term_meta
  ; eq_type_meta = MetaMap.union (f "eq_type_meta" p_meta) a1.eq_type_meta a2.eq_type_meta
  ; eq_term_meta = MetaMap.union (f "eq_term_meta" p_meta) a1.eq_term_meta a2.eq_term_meta
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
    let free = AtomMap.remove x abstr.free
    and bound = BoundSet.add lvl abstr.bound in
    { abstr with free ; bound }
  else
    abstr
