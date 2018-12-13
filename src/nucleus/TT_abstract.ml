(** Abstract *)

open Jdg_typedefs

let rec term x ?(lvl=0) = function
  | (TermAtom {atom_name=y; atom_type=t}) as e ->
     begin match Name.eq_atom x y with
     | false ->
        let asmp = TT_assumption.ty t in
        if Assumption.mem_atom x asmp
        then TT_error.raise InvalidAbstraction
        else e
     | true -> TermBound lvl
     end

  | TermBound k as e ->
     if k < lvl then
       e
     else
       assert false
       (* we should never get here because abstracting
          should always introduce a highest-level bound
          index. *)

  | TermConstructor (c, args) ->
     let args = arguments x ~lvl args in
     TermConstructor (c, args)

  | TermMeta (mv, args) ->
     let args = term_arguments x ~lvl args
     and mv = term_meta x ~lvl mv in
     TermMeta (mv, args)

  | TermConvert (c, asmp, t) ->
     let asmp = Assumption.abstract x ~lvl asmp
     and t = ty x ~lvl t in
     TermConvert (c, asmp, t)

and ty x ?(lvl=0) = function
  | TypeConstructor (c, args) ->
     let args = arguments x ~lvl args in
     TypeConstructor (c, args)
  | TypeMeta (mv, args) ->
     let args = term_arguments x ~lvl args
     and mv = type_meta x ~lvl mv in
     TypeMeta (mv, args)

(* the type of a meta can't refer to bound variables nor to atoms *)
and term_meta x ~lvl mv =
  (* XXX delete me *)
  (* let {meta_name; meta_type} = mv in
   * let meta_type = abstract_abstraction ty x ~lvl meta_type in
   * {meta_name; meta_type} *)
  mv

(* the type of a meta can't refer to bound variables nor to atoms *)
and type_meta x ~lvl mv =
  (* XXX delete me *)
  (* let {meta_name; meta_type} = mv in
   * let meta_type = abstract_abstraction (fun x ?lvl () -> ()) x ~lvl meta_type in
   * {meta_name; meta_type} *)
  mv

and arguments x ?(lvl=0) args =
  List.map (argument x ~lvl) args

and term_arguments x ?(lvl=0) args =
  List.map (term x ~lvl) args

and argument x ?(lvl=0) = function

    | ArgumentIsType t -> ArgumentIsType (abstraction ty x ~lvl t)

    | ArgumentIsTerm e -> ArgumentIsTerm (abstraction term x ~lvl e)

    | ArgumentEqType asmp ->
       let asmp = abstraction eq_type x ~lvl asmp in
       ArgumentEqType asmp

    | ArgumentEqTerm asmp ->
       let asmp = abstraction eq_term x ~lvl asmp in
       ArgumentEqTerm asmp

and assumptions x ?(lvl=0) asmp =
  Assumption.abstract x ~lvl asmp

and eq_type x ?(lvl=0) (EqType (asmp, t1, t2)) =
  let asmp = assumptions x ~lvl asmp
  and t1 = ty x ~lvl t1
  and t2 = ty x ~lvl t2
  in EqType (asmp, t1, t2)

and eq_term x ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  let asmp = assumptions x ~lvl asmp
  and e1 = term x ~lvl e1
  and e2 = term x ~lvl e2
  and t = ty x ~lvl t
  in EqTerm (asmp, e1, e2, t)

and abstraction
  : 'a . (Name.atom -> ?lvl:int -> 'a -> 'a) ->
         Name.atom -> ?lvl:int -> 'a abstraction -> 'a abstraction
  = fun abstr_v x ?(lvl=0) ->
  function
  | NotAbstract v ->
     let v = abstr_v x ~lvl v in
     NotAbstract v

  | Abstract (y, u, abstr) ->
     let u = ty x ~lvl u in
     let abstr = abstraction abstr_v x ~lvl:(lvl+1) abstr in
     Abstract (y, u, abstr)



(***** from Jdg *****)


let not_abstract u = TT_mk.not_abstract u

let is_type_abstraction {atom_name=x; atom_type=t} abstr =
  (* XXX occurs check?! *)
  let abstr = abstraction ty x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let is_term_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction term x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let eq_type_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction eq_type x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let eq_term_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction eq_term x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let boundary_is_type_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction (fun _a ?lvl t -> ()) x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let boundary_is_term_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction ty x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let boundary_eq_type_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction
      (fun a ?lvl (lhs, rhs) ->
         let lhs = ty ?lvl a lhs
         and rhs = ty ?lvl a rhs in
      (lhs, rhs))
      x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

let boundary_eq_term_abstraction {atom_name=x; atom_type=t} abstr =
  let abstr = abstraction
      (fun a ?lvl (lhs, rhs, t) ->
         let lhs = term ?lvl a lhs
         and rhs = term ?lvl a rhs
         and t = ty ?lvl a t in
      (lhs, rhs, t))
      x abstr in
  TT_mk.abstract (Name.ident_of_atom x) t abstr

