open Jdg_typedefs

let fresh_atom x t =
  let x = Name.fresh x in
  { atom_name = x; atom_type = t }

let mk_atom a = TermAtom a

let fresh_meta x abstr = { meta_name = Name.fresh_meta x ; meta_type = abstr }
let fresh_type_meta = fresh_meta
let fresh_term_meta = fresh_meta
let fresh_eq_type_meta = fresh_meta
let fresh_eq_term_meta = fresh_meta

let mk_bound k = TermBound k

let mk_type_constructor c args = TypeConstructor (c, args)

let mk_type_meta m args = TypeMeta (m, args)

let mk_term_constructor c args = TermConstructor (c, args)

let mk_term_meta m args = TermMeta (m, args)

let mk_term_convert e asmp t =
  match e with
  | TermConvert _ -> assert false
  | _ -> TermConvert (e, asmp, t)

let mk_arg_is_type t = ArgIsType t
let mk_arg_is_term e = ArgIsTerm e
let mk_arg_eq_type s = ArgEqType s
let mk_arg_eq_term s = ArgEqTerm s

let mk_eq_type asmp t1 t2 = EqType (asmp, t1, t2)

let mk_eq_term asmp e1 e2 t = EqTerm (asmp, e1, e2, t)

let mk_not_abstract e = NotAbstract e

let mk_abstract x t abstr = Abstract (x, t, abstr)
