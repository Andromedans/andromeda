(** Unabstract *)

let ty x t1 t2 =
  let a = TT_mk.fresh_atom x t1 in
  a, TT_instantiate.ty (TT_mk.atom a) t2

let term x t e =
  let a = TT_mk.fresh_atom x t in
  a, TT_instantiate.term (TT_mk.atom a) e

let eq_type x t eq =
  let a = TT_mk.fresh_atom x t in
  a, TT_instantiate.eq_type (TT_mk.atom a) eq

let eq_term x t eq =
  let a = TT_mk.fresh_atom x t in
  a, TT_instantiate.eq_term (TT_mk.atom a) eq

let abstraction instantiate_u x t abstr =
  let a = TT_mk.fresh_atom x t in
  a, TT_instantiate.abstraction instantiate_u (TT_mk.atom a) abstr
