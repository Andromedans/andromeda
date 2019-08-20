(** Manipulation of assumptions. *)
open Nucleus_types

(** Collect the assumptions of a type. Caveat: alpha-equal types may have
    different assumptions. *)
let rec is_type ?(lvl=0) = function
  | TypeMeta (mv, args) ->
     let args = term_arguments ~lvl args
     and mv = meta ~lvl mv in
     Assumption.union mv args

  | TypeConstructor (_, args) -> arguments' ~lvl args

and is_term ?(lvl=0) = function

  | TermBoundVar k ->
     if k < lvl then
       Assumption.empty
     else
       Assumption.singleton_bound (k - lvl)

  | TermAtom {atom_nonce=x; atom_type=t} ->
     Assumption.add_free_var x t (is_type ~lvl t)

  | TermMeta (mv, args) ->
     let mv = meta ~lvl mv
     and args = term_arguments ~lvl args in
     Assumption.union mv args

  | TermConstructor (_, args) ->
     arguments' ~lvl args

  | TermConvert (e, asmp', t) ->
     Assumption.union
       asmp'
       (Assumption.union (is_term ~lvl e) (is_type ~lvl t))

and eq_type ?(lvl=0) (EqType (asmp, t1, t2)) =
  Assumption.union
    (assumptions ~lvl asmp)
    (Assumption.union (is_type ~lvl t1) (is_type ~lvl t2))

and eq_term ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  Assumption.union
    (Assumption.union (assumptions ~lvl asmp) (is_type ~lvl t))
    (Assumption.union (is_term ~lvl e1) (is_term ~lvl e2))

and meta ~lvl = function
  | MetaFree {meta_nonce; meta_boundary} ->
     let asmp = abstraction boundary ~lvl meta_boundary in
     Assumption.add_free_meta meta_nonce meta_boundary asmp

  | MetaBound k -> Assumption.add_bound_meta k Assumption.empty

and abstraction
  : 'a . (?lvl:bound -> 'a -> assumption) ->
    ?lvl:bound -> 'a abstraction -> assumption
  = fun asmp_v ?(lvl=0) -> function
    | NotAbstract v -> asmp_v ~lvl v
    | Abstract (_, t, abstr) ->
       Assumption.union
         (is_type ~lvl t)
         (abstraction asmp_v ~lvl:(lvl+1) abstr)

and argument ?(lvl=0) = function
  | Arg_NotAbstract jdg -> judgement ~lvl jdg
  | Arg_Abstract (_, arg) -> argument ~lvl:(lvl+1) arg

and term_arguments ~lvl ts =
  List.fold_left
    (fun acc arg -> Assumption.union acc (is_term ~lvl arg))
    Assumption.empty
    ts

and arguments' ~lvl args =
  let rec fold asmp = function
    | [] -> asmp
    | arg :: args -> Assumption.union (argument ~lvl arg) (fold asmp args)
  in
  fold Assumption.empty args

and judgement ?(lvl=0) = function
  | JudgementIsType t -> is_type ~lvl t
  | JudgementIsTerm e -> is_term ~lvl e
  | JudgementEqType eq -> eq_type ~lvl eq
  | JudgementEqTerm eq -> eq_term ~lvl eq

and assumptions ?(lvl=0) asmp = Assumption.at_level ~lvl asmp

and is_type_boundary = Assumption.empty

and is_term_boundary ?(lvl=0) t = is_type ~lvl t

and eq_type_boundary ?(lvl=0) (t1, t2) =
  Assumption.union (is_type ~lvl t1) (is_type ~lvl t2)

and eq_term_boundary ?(lvl=0) (e1, e2, t) =
  Assumption.union
    (is_type ~lvl t)
    (Assumption.union (is_term ~lvl e1) (is_term ~lvl e2))

and boundary ?(lvl=0) = function
  | BoundaryIsType () -> is_type_boundary
  | BoundaryIsTerm t -> is_term_boundary ~lvl t
  | BoundaryEqType eq -> eq_type_boundary ~lvl eq
  | BoundaryEqTerm eq -> eq_term_boundary ~lvl eq

let arguments = arguments' ~lvl:0

let context_u assumptions_u t =
  let asmp = assumptions_u t in
  let {free_var; bound_var; _} = asmp in
  assert (Bound_set.is_empty bound_var) ;
  let free = Nonce.map_bindings free_var in
  List.map (fun (atom_nonce, atom_type) -> {atom_nonce; atom_type}) free

(** Compute the list of atoms occurring in an abstraction. Similar to
    assumptions_XYZ functions, but allows use of the assumptions as atoms.
    May only be called on closed terms. *)
let context_of_abstraction assumptions_u =
  context_u (abstraction ?lvl:None assumptions_u)
