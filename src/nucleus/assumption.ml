open Nucleus_types

let empty =
  { free = Nonce.map_empty
  ; is_type_meta = Nonce.map_empty
  ; is_term_meta = Nonce.map_empty
  ; eq_type_meta = Nonce.map_empty
  ; eq_term_meta = Nonce.map_empty
  ; bound = Bound_set.empty }

let is_empty {free; is_type_meta; is_term_meta; eq_type_meta; eq_term_meta; bound } =
  Nonce.map_is_empty free
  && Nonce.map_is_empty is_type_meta
  && Nonce.map_is_empty is_term_meta
  && Nonce.map_is_empty eq_type_meta
  && Nonce.map_is_empty eq_term_meta
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

let add_is_type_meta x t asmp = { asmp with is_type_meta = Nonce.map_add x t asmp.is_type_meta }
let add_is_term_meta x t asmp = { asmp with is_term_meta = Nonce.map_add x t asmp.is_term_meta }
let add_eq_type_meta x t asmp = { asmp with eq_type_meta = Nonce.map_add x t asmp.eq_type_meta }
let add_eq_term_meta x t asmp = { asmp with eq_term_meta = Nonce.map_add x t asmp.eq_term_meta }

let add_bound k asmp = { asmp with bound = Bound_set.add k asmp.bound }

let union a1 a2 =
  (* XXX figure out why this is happening, fix it, and remove the code below. *)
  let f = (fun vtype a t1 t2 ->
      (if not (t1 == t2)
       then
         (Print.error "XXX %s variable %t occurs at physically different types@." vtype (Nonce.print ~parentheses:false a)
         ; assert false )
       else ()) ;
      Some t1) in
  let f_free = f "free"
  in
  { free = Nonce.map_union f_free a1.free a2.free
  ; is_type_meta = Nonce.map_union (f "is_type_meta") a1.is_type_meta a2.is_type_meta
  ; is_term_meta = Nonce.map_union (f "is_term_meta") a1.is_term_meta a2.is_term_meta
  ; eq_type_meta = Nonce.map_union (f "eq_type_meta") a1.eq_type_meta a2.eq_type_meta
  ; eq_term_meta = Nonce.map_union (f "eq_term_meta") a1.eq_term_meta a2.eq_term_meta
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
