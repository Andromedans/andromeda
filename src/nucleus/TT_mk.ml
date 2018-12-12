open Jdg_typedefs

let fresh_atom x t =
  let x = Name.fresh x in
  { atom_name = x; atom_type = t }

let atom a = TermAtom a

let fresh_meta x abstr = { meta_name = Name.fresh_meta x ; meta_type = abstr }
let fresh_type_meta = fresh_meta
let fresh_term_meta = fresh_meta
let fresh_eq_type_meta = fresh_meta
let fresh_eq_term_meta = fresh_meta

let bound k = TermBound k

let type_constructor c args = TypeConstructor (c, args)

let type_meta m args = TypeMeta (m, args)

let term_constructor c args = TermConstructor (c, args)

let term_meta m args = TermMeta (m, args)

let term_convert e asmp t =
  match e with
  | TermConvert _ -> assert false
  | _ -> TermConvert (e, asmp, t)

let arg_is_type t = ArgumentIsType t
let arg_is_term e = ArgumentIsTerm e
let arg_eq_type s = ArgumentEqType s
let arg_eq_term s = ArgumentEqTerm s

let eq_type asmp t1 t2 = EqType (asmp, t1, t2)

let eq_term asmp e1 e2 t = EqTerm (asmp, e1, e2, t)

let not_abstract e = NotAbstract e

let abstract x t abstr = Abstract (x, t, abstr)
