(** Substitute *)

open TT_abstract
open TT_instantiate

let substitute_term e0 x e =
  let e = abstract_term x e in
  instantiate_term e0 e

let substitute_type e0 x t =
  let t = abstract_type x t in
  instantiate_type e0 t
