open Nucleus_types

let empty =
  { free_var = Nonce.map_empty
  ; free_meta = Nonce.map_empty
  ; bound_var = Bound_set.empty
  ; bound_meta = Bound_set.empty
  }

let is_empty {free_var; free_meta; bound_var; bound_meta} =
  Nonce.map_is_empty free_var
  && Nonce.map_is_empty free_meta
  && Bound_set.is_empty bound_var
  && Bound_set.is_empty bound_meta

let mem_free_var x s = Nonce.map_mem x s.free_var

let mem_bound_var k s = Bound_set.mem k s.bound_var

(** [at_level ~lvl asmp] removes bound variables below [lvl] and subtracts [lvl] from the other ones. *)
let at_level ~lvl s =
  { s with
    bound_var = Bound_set.fold
        (fun k s -> if k < lvl then s else Bound_set.add (k - lvl) s)
        s.bound_var Bound_set.empty }

(** [shift ~lvl k asmp] shifts bound variables above [lvl] by [k]. *)
let shift ~lvl k s =
  { s with
    bound_var =
      Bound_set.fold
        (fun j s -> Bound_set.add (if j < lvl then j else j + k) s)
        s.bound_var
        Bound_set.empty }

(** [shift_meta k asmp] shifts bound meta-variables by [k]. *)
let shift_meta k s =
  { s with bound_meta = Bound_set.map (fun j -> j + k) s.bound_meta }

let singleton_bound k = { empty with bound_var = Bound_set.singleton k }

let add_free_var x t asmp = { asmp with free_var = Nonce.map_add x t asmp.free_var }

let add_free_meta x t asmp = { asmp with free_meta = Nonce.map_add x t asmp.free_meta }

let add_bound_var k asmp = { asmp with bound_var = Bound_set.add k asmp.bound_var }

let add_bound_meta k asmp = { asmp with bound_meta = Bound_set.add k asmp.bound_meta }

let union a1 a2 =
  (* We arbitrarily pick the first type because they're supposed to be equal. It
     would be more paranoid to check that they are equal and complain if not
     (this shouldn't happen). *)
  { free_var = Nonce.map_union (fun _ t _ -> Some t) a1.free_var a2.free_var
  ; free_meta = Nonce.map_union (fun _ bdry _ -> Some bdry) a1.free_meta a2.free_meta
  ; bound_var = Bound_set.union a1.bound_var a2.bound_var
  ; bound_meta = Bound_set.union a1.bound_meta a2.bound_meta
  }

(** [instantiate_bound asmp0 ~lvl:k asmp] replaces bound variable [k] with the assumptions [asmp0] in [asmp]. *)
let instantiate_bound asmp0 ~lvl asmp =
  match Bound_set.mem lvl asmp.bound_var with
  | false -> asmp
  | true ->
     let bound0 = Bound_set.map (fun k -> lvl + k) asmp0.bound_var
     and bound_var = Bound_set.remove lvl asmp.bound_var in
     (** Meta-variables do not contain bound variables *)
     let asmp0 = {asmp0 with bound_var = bound0}
     and asmp = {asmp with bound_var} in
     union asmp asmp0

(** [fully_instantiate asmps ~lvl:k asmp] replaces bound variables in [asmp] with assumptions [asmps]. *)
let fully_instantiate_bound asmps ~lvl asmp =
  let rec fold asmp = function
    | [] -> asmp
    | asmp0 :: asmps ->
       let asmp = instantiate_bound asmp0 ~lvl asmp
       in fold asmp asmps
  in
  fold asmp asmps

(** [abstract x ~lvl:k l] replaces the free variable [x] by the bound variable [k]. *)
let abstract x ~lvl abstr =
  if Nonce.map_mem x abstr.free_var
  then
    let free_var = Nonce.map_remove x abstr.free_var
    and bound_var = Bound_set.add lvl abstr.bound_var in
    { abstr with free_var ; bound_var }
  else
    abstr

(** Compute the assumption set of a type expression, fail if a bound meta-variable is
    encountered. *)
let rec of_is_type ~lvl = function

  | TypeMeta (MetaBound _, _) -> assert false

  | TypeMeta (MetaFree {meta_nonce=mv; meta_boundary=bdry}, ts) ->
     add_free_meta mv bdry (of_is_terms ~lvl ts)

  | TypeConstructor (_, args) ->
     of_arguments ~lvl args

(** Compute the assumption set of a term expression, fail if a bound meta-variable is
    encountered. *)
and of_is_term ~lvl = function

  | TermBoundVar k ->
     if k < lvl then empty else singleton_bound (k - lvl)

  | TermAtom {atom_nonce=atm; atom_type=ty} ->
     (** XXX should we include the assumptions of ty? *)
     add_free_var atm ty empty

  | TermMeta (MetaBound _, _) -> assert false

  | TermMeta (MetaFree {meta_nonce=mv; meta_boundary=bdry}, ts) ->
     (** XXX should we include the assumptions of bdry? *)
     add_free_meta mv bdry (of_is_terms ~lvl ts)

  | TermConstructor (_, args) ->
     of_arguments ~lvl args

  | TermConvert (e, asmp, t) ->
     union (at_level ~lvl asmp) (union (of_is_term ~lvl e) (of_is_type ~lvl t))

(** Compute the assumption set of a list of terms, fail if a bound meta-variable is
    encountered. *)
and of_is_terms ~lvl = function
  | [] -> empty
  | t :: ts -> union (of_is_term ~lvl t) (of_is_terms ~lvl ts)

(** Compute the assumption set of an argument *)
and of_argument ~lvl = function
  | Arg_NotAbstract jdg -> of_judgement ~lvl jdg
  | Arg_Abstract (_, arg) -> of_argument ~lvl:(lvl+1) arg

(** Compute the assumption set of a list of arguments *)
and of_arguments ~lvl = function
  | [] -> empty
  | arg :: args -> union (of_argument ~lvl arg) (of_arguments ~lvl args)

(** Compute the assumption set of a judgement *)
and of_judgement ~lvl = function

  | JudgementIsType t ->
     of_is_type ~lvl t

  | JudgementIsTerm e ->
     of_is_term ~lvl e

  | JudgementEqType (EqType (asmp, t1, t2)) ->
     union (union (at_level ~lvl asmp) (of_is_type ~lvl t1)) (of_is_type ~lvl t2)

  | JudgementEqTerm (EqTerm (asmp, e1, e2, t)) ->
     union
       (union
          (union
             (at_level ~lvl asmp)
             (of_is_type ~lvl t))
          (of_is_term ~lvl e1))
       (of_is_term ~lvl e2)
