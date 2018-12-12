(** Manipulation of assumptions. *)
open Jdg_typedefs

(** The assumptions of a term [e] are the atoms and bound variables appearing in [e]. *)
let rec assumptions_term ?(lvl=0) = function

  | TermAtom {atom_name=x; atom_type=t} ->
     Assumption.add_free x t (assumptions_type ~lvl t)

  | TermBound k ->
     if k < lvl then
       Assumption.empty
     else
       Assumption.singleton_bound (k - lvl)

  | TermConstructor (_, args) ->
     assumptions_arguments ~lvl args

  | TermMeta (mv, args) ->
     let mv = assumptions_term_meta ~lvl mv
     and args = assumptions_term_args ~lvl args in
     Assumption.union mv args

  | TermConvert (e, asmp', t) ->
     Assumption.union
       asmp'
       (Assumption.union (assumptions_term ~lvl e) (assumptions_type ~lvl t))

and assumptions_term_meta ~lvl {meta_name; meta_type} =
  let asmp = assumptions_abstraction assumptions_type ~lvl meta_type in
  Assumption.add_is_term_meta meta_name meta_type asmp

and assumptions_type ?(lvl=0) = function
  | TypeConstructor (_, args) -> assumptions_arguments ~lvl args
  | TypeMeta (mv, args) ->
     let args = assumptions_term_args ~lvl args
     and mv = assumptions_type_meta ~lvl mv in
     Assumption.union mv args

and assumptions_type_meta ~lvl {meta_name; meta_type} =
  let asmp =
    assumptions_abstraction (fun ?lvl () -> Assumption.empty) ~lvl meta_type
  in
  Assumption.add_is_type_meta meta_name meta_type asmp

and assumptions_term_args ~lvl ts =
  List.fold_left
    (fun acc arg -> Assumption.union acc (assumptions_term ~lvl arg))
    Assumption.empty
    ts

and assumptions_arguments ~lvl args =
  let rec fold asmp = function
    | [] -> asmp
    | arg :: args -> Assumption.union (assumptions_argument ~lvl arg) (fold asmp args)
  in
  fold Assumption.empty args

and assumptions_eq_type ?(lvl=0) (EqType (asmp, t1, t2)) =
  Assumption.union
    (assumptions_assumptions ~lvl asmp)
    (Assumption.union (assumptions_type ~lvl t1) (assumptions_type ~lvl t2))

and assumptions_eq_term ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  Assumption.union
    (Assumption.union (assumptions_assumptions ~lvl asmp) (assumptions_type ~lvl t))
    (Assumption.union (assumptions_term ~lvl e1) (assumptions_term ~lvl e2))

and assumptions_argument ?(lvl=0) = function
  | ArgIsType abstr -> assumptions_abstraction assumptions_type ~lvl abstr
  | ArgIsTerm abstr -> assumptions_abstraction assumptions_term ~lvl abstr
  | ArgEqType abstr -> assumptions_abstraction assumptions_eq_type ~lvl abstr
  | ArgEqTerm abstr -> assumptions_abstraction assumptions_eq_term ~lvl abstr

and assumptions_assumptions ?(lvl=0) asmp = Assumption.at_level ~lvl asmp

and assumptions_abstraction
  : 'a . (?lvl:bound -> 'a -> assumption) ->
        ?lvl:bound -> 'a abstraction -> assumption
 = fun asmp_v ?(lvl=0) -> function
  | NotAbstract v -> asmp_v ~lvl v
  | Abstract (x, u, abstr) ->
     Assumption.union
       (assumptions_type ~lvl u)
       (assumptions_abstraction asmp_v ~lvl:(lvl+1) abstr)

let assumptions_arguments = assumptions_arguments ~lvl:0

let context_u assumptions_u t =
  let asmp = assumptions_u t in
  let free, _is_type_meta, _, _, _, bound = Assumption.unpack asmp in
  assert (Assumption.BoundSet.is_empty bound) ;
  let free = Name.AtomMap.bindings free in
  List.map (fun (atom_name, atom_type) -> {atom_name; atom_type}) free

let context_abstraction assumptions_u =
  context_u (assumptions_abstraction ?lvl:None assumptions_u)
