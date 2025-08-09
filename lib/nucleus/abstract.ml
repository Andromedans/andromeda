(** Abstract *)

open Nucleus_types

(** [abstract_is_type x ~lvl:k t] replaces atom whose nonce is [x] in type [t] with bound variable [k] (default [0]). *)
let rec is_type x ?(lvl=0) = function

  | TypeConstructor (c, args) ->
     let args = arguments x ~lvl args in
     TypeConstructor (c, args)

  | TypeMeta (mv, args) ->
     let args = term_arguments x ~lvl args
     and mv = meta x ~lvl mv in
     TypeMeta (mv, args)

and is_term x ?(lvl=0) = function
  | TermBoundVar k as e ->
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
        if Assumption.mem_free_var x asmp
        then Error.raise InvalidAbstraction
        else e
     | true -> TermBoundVar lvl
     end

  | TermMeta (mv, args) ->
     let args = term_arguments x ~lvl args
     and mv = meta x ~lvl mv in
     TermMeta (mv, args)

  | TermConstructor (c, args) ->
     let args = arguments x ~lvl args in
     TermConstructor (c, args)

  | TermConvert (e, asmp, t) ->
     let e = is_term x ~lvl e
     and asmp = Assumption.abstract x ~lvl asmp
     and t = is_type x ~lvl t in
     (* does not create a doubly nested [TermConvert] because original input does not either *)
     TermConvert (e, asmp, t)

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

and meta x ~lvl:_ = function

    | MetaBound _ as mv -> mv

    | MetaFree {meta_boundary; _} as mv ->
       (* the type of a meta can't refer to bound variables nor to atoms *)
       if Occurs_atom.abstraction Occurs_atom.boundary x meta_boundary then
         Error.raise InvalidAbstraction
       else
         mv

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

    | Abstract (y, u, abstr) ->
       let u = is_type x ~lvl u in
       let abstr = abstraction abstr_v x ~lvl:(lvl+1) abstr in
       Abstract (y, u, abstr)

and term_arguments x ?(lvl=0) args = List.map (is_term x ~lvl) args

and argument x ?(lvl=0) = function
  | Arg_NotAbstract jdg -> Arg_NotAbstract (judgement x ~lvl jdg)
  | Arg_Abstract (y, arg) -> Arg_Abstract (y, argument x ~lvl:(lvl+1) arg)

and arguments x ?(lvl=0) args = List.map (argument x ~lvl) args

and judgement x ?(lvl=0) = function
  | JudgementIsType t -> JudgementIsType (is_type x ~lvl t)

  | JudgementIsTerm e -> JudgementIsTerm (is_term x ~lvl e)

  | JudgementEqType asmp -> JudgementEqType (eq_type x ~lvl asmp)

  | JudgementEqTerm asmp -> JudgementEqTerm (eq_term x ~lvl asmp)

let not_abstract u = Mk.not_abstract u

let is_type_abstraction ?name {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction is_type n abstr in
  let x = match name with Some x -> x | None -> Nonce.name n in
  Mk.abstract x t abstr

let is_term_abstraction ?name {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction is_term n abstr in
  let x = match name with Some x -> x | None -> Nonce.name n in
  Mk.abstract x t abstr

let eq_type_abstraction ?name {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction eq_type n abstr in
  let x = match name with Some x -> x | None -> Nonce.name n in
  Mk.abstract x t abstr

let eq_term_abstraction ?name {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction eq_term n abstr in
  let x = match name with Some x -> x | None -> Nonce.name n in
  Mk.abstract x t abstr

let judgement_abstraction ?name {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction judgement n abstr in
  let x = match name with Some x -> x | None -> Nonce.name n in
  Mk.abstract x t abstr

let boundary_is_type _atm ?lvl:_ () = ()

let boundary_is_term atm ?lvl t = is_type atm ?lvl t

let boundary_eq_type atm ?lvl (lhs, rhs) =
  let lhs = is_type ?lvl atm lhs
  and rhs = is_type ?lvl atm rhs in
  (lhs, rhs)

let boundary_eq_term atm ?lvl (lhs, rhs, t) =
  let lhs = is_term ?lvl atm lhs
  and rhs = is_term ?lvl atm rhs
  and t = is_type ?lvl atm t in
  (lhs, rhs, t)

let boundary atm ?lvl = function
  | BoundaryIsType bdry -> BoundaryIsType (boundary_is_type atm ?lvl bdry)
  | BoundaryIsTerm bdry -> BoundaryIsTerm (boundary_is_term atm ?lvl bdry)
  | BoundaryEqType bdry -> BoundaryEqType (boundary_eq_type atm ?lvl bdry)
  | BoundaryEqTerm bdry -> BoundaryEqTerm (boundary_eq_term atm ?lvl bdry)

let boundary_is_type_abstraction {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction boundary_is_type n abstr in
  Mk.abstract (Nonce.name n) t abstr

let boundary_is_term_abstraction {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction boundary_is_term n abstr in
  Mk.abstract (Nonce.name n) t abstr

let boundary_eq_type_abstraction {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction boundary_eq_type n abstr in
  Mk.abstract (Nonce.name n) t abstr

let boundary_eq_term_abstraction {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction boundary_eq_term n abstr in
  Mk.abstract (Nonce.name n) t abstr

let boundary_abstraction {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction boundary n abstr in
  Mk.abstract (Nonce.name n) t abstr

let judgement_with_boundary x ?(lvl=0) (jdg, bdry) =
  (judgement x ~lvl jdg, boundary x ~lvl bdry)

let judgement_with_boundary_abstraction {atom_nonce=n; atom_type=t} abstr =
  let abstr = abstraction judgement_with_boundary n abstr in
  Mk.abstract (Nonce.name n) t abstr
