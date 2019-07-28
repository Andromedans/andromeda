open Nucleus_types

let empty =
  { free = Nonce.map_empty
  ; meta = Nonce.map_empty
  ; bound = Bound_set.empty }

let is_empty {free; meta; bound } =
  Nonce.map_is_empty free
  && Nonce.map_is_empty meta
  && Bound_set.is_empty bound

let mem_atom x s = Nonce.map_mem x s.free

let mem_bound k s = Bound_set.mem k s.bound

(** [at_level ~lvl asmp] removes bound variables below [lvl] and subtracts [lvl] from the other ones. *)
let at_level ~lvl s =
  { s with
    bound = Bound_set.fold
        (fun k s -> if k < lvl then s else Bound_set.add (k - lvl) s)
        s.bound Bound_set.empty }

(** [shift ~lvl k asmp] shifts bound variables above [lvl] by [k]. *)
let shift ~lvl k s =
  { s with
    bound =
      Bound_set.fold
        (fun j s -> Bound_set.add (if j < lvl then j else j + k) s)
        s.bound
        Bound_set.empty }

let singleton_bound k = { empty with bound = Bound_set.singleton k }

let add_free x t asmp = { asmp with free = Nonce.map_add x t asmp.free }

let add_meta x t asmp = { asmp with meta = Nonce.map_add x t asmp.meta }

let add_bound k asmp = { asmp with bound = Bound_set.add k asmp.bound }

let union a1 a2 =
  (* We arbitrarily pick the first type because they're supposed to be equal. It
     would be more paranoid to check that they are equal and complain if not
     (this shouldn't happen). *)
  { free = Nonce.map_union (fun _ t _ -> Some t) a1.free a2.free
  ; meta = Nonce.map_union (fun _ bdry _ -> Some bdry) a1.meta a2.meta
  ; bound = Bound_set.union a1.bound a2.bound
  }

(** [instantiate asmp0 ~lvl:k asmp] replaces bound variable [k] with the assumptions [asmp0] in [asmp]. *)
let instantiate asmp0 ~lvl asmp =
  match Bound_set.mem lvl asmp.bound with
  | false -> asmp
  | true ->
     let bound0 = Bound_set.map (fun k -> lvl + k) asmp0.bound
     and bound = Bound_set.remove lvl asmp.bound
     in
     let asmp0 = {asmp0 with bound = bound0}
     and asmp = {asmp with bound} in
     union asmp asmp0

(** [fully_instantiate asmps ~lvl:k asmp] replaces bound variables in [asmp] with assumptions [asmps]. *)
let fully_instantiate asmps ~lvl asmp =
  let rec fold asmp = function
    | [] -> asmp
    | asmp0 :: asmps ->
       let asmp = instantiate asmp0 ~lvl asmp
       in fold asmp asmps
  in
  fold asmp asmps

(** [abstract x ~lvl:k l] replaces the free variable [x] by the bound variable [k]. *)
let abstract x ~lvl abstr =
  if Nonce.map_mem x abstr.free
  then
    let free = Nonce.map_remove x abstr.free
    and bound = Bound_set.add lvl abstr.bound in
    { abstr with free ; bound }
  else
    abstr
