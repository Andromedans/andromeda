(** Abstract *)

open Nucleus_types

(** [abstract_is_type x0 ~lvl:k t] replaces atom [x0] in type [t] with bound variable [k] (default [0]). *)
let rec is_type x ?(lvl=0) = function
  | TypeConstructor (c, args) ->
     let args = arguments x ~lvl args in
     TypeConstructor (c, args)
  | TypeMeta (mv, args) ->
     let args = term_arguments x ~lvl args
     and mv = is_type_meta x ~lvl mv in
     TypeMeta (mv, args)

and is_term x ?(lvl=0) = function
  | TermBound k as e ->
     if k < lvl then
       e
     else
       assert false
  (* we should never get here because abstracting should always introduce a
     highest-level bound index. *)

  | (TermAtom {atom_nonce=y; atom_type=t}) as e ->
     begin match Nonce.equal x y with
     | false ->
        let asmp = Collect_assumptions.is_type t in
        if Assumption.mem_atom x asmp
        then Error.raise InvalidAbstraction
        else e
     | true -> TermBound lvl
     end

  | TermMeta (mv, args) ->
     let args = term_arguments x ~lvl args
     and mv = is_term_meta x ~lvl mv in
     TermMeta (mv, args)

  | TermConstructor (c, args) ->
     let args = arguments x ~lvl args in
     TermConstructor (c, args)

  | TermConvert (c, asmp, t) ->
     let asmp = Assumption.abstract x ~lvl asmp
     and t = is_type x ~lvl t in
     TermConvert (c, asmp, t)

and eq_type x ?(lvl=0) (EqType (asmp, t1, t2)) =
  let asmp = assumptions x ~lvl asmp
  and t1 = is_type x ~lvl t1
  and t2 = is_type x ~lvl t2
  in EqType (asmp, t1, t2)

and eq_term x ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  let asmp = assumptions x ~lvl asmp
  and e1 = is_term x ~lvl e1
  and e2 = is_term x ~lvl e2
  and t = is_type x ~lvl t
  in EqTerm (asmp, e1, e2, t)

(* the type of a meta can't refer to bound variables nor to atoms *)
and is_term_meta x ~lvl mv = mv

(* the type of a meta can't refer to bound variables nor to atoms *)
and is_type_meta x ~lvl mv = mv

and assumptions x ?(lvl=0) asmp =
  Assumption.abstract x ~lvl asmp

and abstraction
  : 'a . (Nonce.t -> ?lvl:int -> 'a -> 'a) ->
    Nonce.t -> ?lvl:int -> 'a abstraction -> 'a abstraction
  = fun abstr_v x ?(lvl=0) ->
    function
    | NotAbstract v ->
       let v = abstr_v x ~lvl v in
       NotAbstract v

    | Abstract ({atom_nonce=y; atom_type=u}, abstr) ->
       let u = is_type x ~lvl u in
       let abstr = abstraction abstr_v x ~lvl:(lvl+1) abstr in
       Abstract ({atom_nonce=y; atom_type=u}, abstr)

and term_arguments x ?(lvl=0) args = List.map (is_term x ~lvl) args

and arguments x ?(lvl=0) args = List.map (argument x ~lvl) args

and argument x ?(lvl=0) = function

  | JudgementIsType t -> JudgementIsType (abstraction is_type x ~lvl t)

  | JudgementIsTerm e -> JudgementIsTerm (abstraction is_term x ~lvl e)

  | JudgementEqType asmp ->
     let asmp = abstraction eq_type x ~lvl asmp in
     JudgementEqType asmp

  | JudgementEqTerm asmp ->
     let asmp = abstraction eq_term x ~lvl asmp in
     JudgementEqTerm asmp

let not_abstract u = Mk.not_abstract u

let judgement atm jdg = argument atm.atom_nonce jdg

let is_type_abstraction atm abstr =
  (* XXX occurs check?! *)
  let abstr = abstraction is_type atm.atom_nonce abstr in
  Mk.abstract atm abstr

let is_term_abstraction atm abstr =
  let abstr = abstraction is_term atm.atom_nonce abstr in
  Mk.abstract atm abstr

let eq_type_abstraction atm abstr =
  let abstr = abstraction eq_type atm.atom_nonce abstr in
  Mk.abstract atm abstr

let eq_term_abstraction atm abstr =
  let abstr = abstraction eq_term atm.atom_nonce abstr in
  Mk.abstract atm abstr

let boundary_is_type_abstraction atm abstr =
  let abstr = abstraction (fun _a ?lvl t -> ()) atm.atom_nonce abstr in
  Mk.abstract atm abstr

let boundary_is_term_abstraction atm abstr =
  let abstr = abstraction is_type atm.atom_nonce abstr in
  Mk.abstract atm abstr

let boundary_eq_type_abstraction atm abstr =
  let abstr = abstraction
      (fun a ?lvl (lhs, rhs) ->
         let lhs = is_type ?lvl a lhs
         and rhs = is_type ?lvl a rhs in
         (lhs, rhs))
      atm.atom_nonce abstr in
  Mk.abstract atm abstr

let boundary_eq_term_abstraction atm abstr =
  let abstr = abstraction
      (fun a ?lvl (lhs, rhs, t) ->
         let lhs = is_term ?lvl a lhs
         and rhs = is_term ?lvl a rhs
         and t = is_type ?lvl a t in
         (lhs, rhs, t))
      atm.atom_nonce abstr in
  Mk.abstract atm abstr

let boundary atm = function
  | BoundaryIsTerm abstr -> BoundaryIsTerm (boundary_is_term_abstraction atm abstr)
  | BoundaryIsType abstr -> BoundaryIsType (boundary_is_type_abstraction atm abstr)
  | BoundaryEqType abstr -> BoundaryEqType (boundary_eq_type_abstraction atm abstr)
  | BoundaryEqTerm abstr -> BoundaryEqTerm (boundary_eq_term_abstraction atm abstr)
