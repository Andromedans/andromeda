(** Unabstract *)

let is_type x t1 t2 =
  let a = Mk.fresh_atom x t1 in
  a, Instantiate_bound.is_type (Mk.atom a) t2

let is_term x t e =
  let a = Mk.fresh_atom x t in
  a, Instantiate_bound.is_term (Mk.atom a) e

let eq_type x t eq =
  let a = Mk.fresh_atom x t in
  a, Instantiate_bound.eq_type (Mk.atom a) eq

let eq_term x t eq =
  let a = Mk.fresh_atom x t in
  a, Instantiate_bound.eq_term (Mk.atom a) eq

let abstraction instantiate_u x t abstr =
  let a = Mk.fresh_atom x t in
  a, Instantiate_bound.abstraction instantiate_u (Mk.atom a) abstr
