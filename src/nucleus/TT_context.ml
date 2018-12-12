open Jdg_typedefs

let context_u assumptions_u t =
  let asmp = assumptions_u t in
  let free, _is_type_meta, _, _, _, bound = Assumption.unpack asmp in
  assert (BoundSet.is_empty bound) ;
  let free = Name.AtomMap.bindings free in
  List.map (fun (atom_name, atom_type) -> {atom_name; atom_type}) free

let abstraction assumptions_u =
  context_u (TT_assumption.abstraction ?lvl:None assumptions_u)
