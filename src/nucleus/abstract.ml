(** Abstract *)

open Nucleus_types

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

  | (TermAtom {atom_name=y; atom_type=t}) as e ->
     begin match Name.eq_atom x y with
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
  : 'a . (Name.atom -> ?lvl:int -> 'a -> 'a) ->
    Name.atom -> ?lvl:int -> 'a abstraction -> 'a abstraction
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

and arguments x ?(lvl=0) args = List.map (argument x ~lvl) args

and argument x ?(lvl=0) = function

  | ArgumentIsType t -> ArgumentIsType (abstraction is_type x ~lvl t)

  | ArgumentIsTerm e -> ArgumentIsTerm (abstraction is_term x ~lvl e)

  | ArgumentEqType asmp ->
     let asmp = abstraction eq_type x ~lvl asmp in
     ArgumentEqType asmp

  | ArgumentEqTerm asmp ->
     let asmp = abstraction eq_term x ~lvl asmp in
     ArgumentEqTerm asmp



(***** from Jdg *****)


let not_abstract u = Mk.not_abstract u

let is_type_abstraction {atom_name=x; atom_type=t} abstr =
  (* XXX occurs check?! *)
  let abstr = abstraction is_type x abstr in
  Mk.abstract (Name.ident_of_atom x) t abstr

let is_term_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction is_term x abstr in
  Mk.abstract (Name.ident_of_atom x) t abstr

let eq_type_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction eq_type x abstr in
  Mk.abstract (Name.ident_of_atom x) t abstr

let eq_term_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction eq_term x abstr in
  Mk.abstract (Name.ident_of_atom x) t abstr

let boundary_is_type_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction (fun _a ?lvl t -> ()) x abstr in
  Mk.abstract (Name.ident_of_atom x) t abstr

let boundary_is_term_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction is_type x abstr in
  Mk.abstract (Name.ident_of_atom x) t abstr

let boundary_eq_type_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction
      (fun a ?lvl (lhs, rhs) ->
         let lhs = is_type ?lvl a lhs
         and rhs = is_type ?lvl a rhs in
         (lhs, rhs))
      x abstr in
  Mk.abstract (Name.ident_of_atom x) t abstr

let boundary_eq_term_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction
      (fun a ?lvl (lhs, rhs, t) ->
         let lhs = is_term ?lvl a lhs
         and rhs = is_term ?lvl a rhs
         and t = is_type ?lvl a t in
         (lhs, rhs, t))
      x abstr in
  Mk.abstract (Name.ident_of_atom x) t abstr

