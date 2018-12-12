(** Unabstract *)

open TT_instantiate

let unabstract_type x t1 t2 =
  let a = TT_mk.fresh_atom x t1 in
  a, instantiate_type (TT_mk.atom a) t2

let unabstract_term x t e =
  let a = TT_mk.fresh_atom x t in
  a, instantiate_term (TT_mk.atom a) e

let unabstract_eq_type x t eq =
  let a = TT_mk.fresh_atom x t in
  a, instantiate_eq_type (TT_mk.atom a) eq

let unabstract_eq_term x t eq =
  let a = TT_mk.fresh_atom x t in
  a, instantiate_eq_term (TT_mk.atom a) eq

let unabstract_abstraction instantiate_u x t abstr =
  let a = TT_mk.fresh_atom x t in
  a, instantiate_abstraction instantiate_u (TT_mk.atom a) abstr
