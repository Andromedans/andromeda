(** Substitute *)

let substitute_term e0 x e =
  let e = TT_abstract.term x e in
  TT_instantiate.term e0 e

let substitute_type e0 x t =
  let t = TT_abstract.ty x t in
  TT_instantiate.ty e0 t
