(** Abstract *)

open Jdg_typedefs
open TT_error

let rec abstract_term x ?(lvl=0) = function
  | (TermAtom {atom_name=y; atom_type=t}) as e ->
     begin match Name.eq_atom x y with
     | false ->
        let asmp = TT_assumption.ty t in
        if Assumption.mem_atom x asmp
        then error InvalidAbstraction
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
     let args = abstract_arguments x ~lvl args in
     TermConstructor (c, args)

  | TermMeta (mv, args) ->
     let args = abstract_term_arguments x ~lvl args
     and mv = abstract_term_meta x ~lvl mv in
     TermMeta (mv, args)

  | TermConvert (c, asmp, t) ->
     let asmp = Assumption.abstract x ~lvl asmp
     and t = abstract_type x ~lvl t in
     TermConvert (c, asmp, t)

and abstract_type x ?(lvl=0) = function
  | TypeConstructor (c, args) ->
     let args = abstract_arguments x ~lvl args in
     TypeConstructor (c, args)
  | TypeMeta (mv, args) ->
     let args = abstract_term_arguments x ~lvl args
     and mv = abstract_type_meta x ~lvl mv in
     TypeMeta (mv, args)

(* the type of a meta can't refer to bound variables nor to atoms *)
and abstract_term_meta x ~lvl mv =
  (* XXX delete me *)
  (* let {meta_name; meta_type} = mv in
   * let meta_type = abstract_abstraction abstract_type x ~lvl meta_type in
   * {meta_name; meta_type} *)
  mv

(* the type of a meta can't refer to bound variables nor to atoms *)
and abstract_type_meta x ~lvl mv =
  (* XXX delete me *)
  (* let {meta_name; meta_type} = mv in
   * let meta_type = abstract_abstraction (fun x ?lvl () -> ()) x ~lvl meta_type in
   * {meta_name; meta_type} *)
  mv

and abstract_arguments x ?(lvl=0) args =
  List.map (abstract_argument x ~lvl) args

and abstract_term_arguments x ?(lvl=0) args =
  List.map (abstract_term x ~lvl) args

and abstract_argument x ?(lvl=0) = function

    | ArgIsType t -> ArgIsType (abstract_abstraction abstract_type x ~lvl t)

    | ArgIsTerm e -> ArgIsTerm (abstract_abstraction abstract_term x ~lvl e)

    | ArgEqType asmp ->
       let asmp = abstract_abstraction abstract_eq_type x ~lvl asmp in
       ArgEqType asmp

    | ArgEqTerm asmp ->
       let asmp = abstract_abstraction abstract_eq_term x ~lvl asmp in
       ArgEqTerm asmp

and abstract_assumptions x ?(lvl=0) asmp =
  Assumption.abstract x ~lvl asmp

and abstract_eq_type x ?(lvl=0) (EqType (asmp, t1, t2)) =
  let asmp = abstract_assumptions x ~lvl asmp
  and t1 = abstract_type x ~lvl t1
  and t2 = abstract_type x ~lvl t2
  in EqType (asmp, t1, t2)

and abstract_eq_term x ?(lvl=0) (EqTerm (asmp, e1, e2, t)) =
  let asmp = abstract_assumptions x ~lvl asmp
  and e1 = abstract_term x ~lvl e1
  and e2 = abstract_term x ~lvl e2
  and t = abstract_type x ~lvl t
  in EqTerm (asmp, e1, e2, t)

and abstract_abstraction
  : 'a . (Name.atom -> ?lvl:int -> 'a -> 'a) ->
         Name.atom -> ?lvl:int -> 'a abstraction -> 'a abstraction
  = fun abstr_v x ?(lvl=0) ->
  function
  | NotAbstract v ->
     let v = abstr_v x ~lvl v in
     NotAbstract v

  | Abstract (y, u, abstr) ->
     let u = abstract_type x ~lvl u in
     let abstr = abstract_abstraction abstr_v x ~lvl:(lvl+1) abstr in
     Abstract (y, u, abstr)
