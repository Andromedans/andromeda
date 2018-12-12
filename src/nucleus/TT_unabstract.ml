(** Unabstract *)

open TT_instantiate
open TT_mk

let unabstract_type x t1 t2 =
  let a = fresh_atom x t1 in
  a, instantiate_type (mk_atom a) t2

let unabstract_term x t e =
  let a = fresh_atom x t in
  a, instantiate_term (mk_atom a) e

let unabstract_eq_type x t eq =
  let a = fresh_atom x t in
  a, instantiate_eq_type (mk_atom a) eq

let unabstract_eq_term x t eq =
  let a = fresh_atom x t in
  a, instantiate_eq_term (mk_atom a) eq

let unabstract_abstraction instantiate_u x t abstr =
  let a = fresh_atom x t in
  a, instantiate_abstraction instantiate_u (mk_atom a) abstr
