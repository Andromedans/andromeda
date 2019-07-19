open Nucleus_types

let atom_name {atom_nonce=x;_} = Nonce.name x

(** Destructors *)

let invert_argument = function
  | JudgementIsTerm abstr -> JudgementIsTerm abstr
  | JudgementIsType abstr -> JudgementIsType abstr
  | JudgementEqType abstr -> JudgementEqType abstr
  | JudgementEqTerm abstr -> JudgementEqTerm abstr

let invert_arguments args = List.map invert_argument args

let invert_is_term sgn = function

  | TermAtom a -> Stump_TermAtom a

  | TermBound _ -> assert false

  | TermConstructor (c, args) ->
     let arguments = invert_arguments args in
     Stump_TermConstructor (c, arguments)

  | TermMeta (mv, args) ->
     Stump_TermMeta (mv, args)

  | TermConvert (e, asmp, t) ->
     let t' = Sanity.natural_type sgn e in
     let eq = Mk.eq_type asmp t' t in
     Stump_TermConvert (e, eq)

let invert_is_type = function
  | TypeConstructor (c, args) ->
     let arguments = invert_arguments args in
     Stump_TypeConstructor (c, arguments)
  | TypeMeta (mv, args) -> Stump_TypeMeta (mv, args)

let invert_eq_type (EqType (asmp, t1, t2)) = Stump_EqType (asmp, t1, t2)

let invert_eq_term (EqTerm (asmp, e1, e2, t)) = Stump_EqTerm (asmp, e1, e2, t)

let as_not_abstract = function
  | Abstract _ -> None
  | NotAbstract v -> Some v

let invert_abstraction ?name inst_v = function
  | Abstract ({atom_nonce=x; atom_type=t}, abstr) ->
     let x = (match name with None -> Nonce.name x | Some y -> y) in
     let a = Mk.fresh_atom x t in
     let abstr = Instantiate_bound.abstraction inst_v (Mk.atom a) abstr in
     Stump_Abstract (a, abstr)
  | NotAbstract v -> Stump_NotAbstract v

let invert_is_type_abstraction ?name t =
  invert_abstraction ?name Instantiate_bound.is_type t

let invert_is_term_abstraction ?name e =
  invert_abstraction ?name Instantiate_bound.is_term e

let invert_eq_type_abstraction ?name eq =
  invert_abstraction ?name Instantiate_bound.eq_type eq

let invert_eq_term_abstraction ?name eq =
  invert_abstraction ?name Instantiate_bound.eq_term eq

let invert_is_type_boundary ?name bdry =
  invert_abstraction ?name Instantiate_bound.is_type_boundary bdry

let invert_is_term_boundary ?name bdry =
  invert_abstraction ?name Instantiate_bound.is_term_boundary bdry

let invert_eq_type_boundary ?name bdry =
  invert_abstraction ?name Instantiate_bound.eq_type_boundary bdry

let invert_eq_term_boundary ?name bdry =
  invert_abstraction ?name Instantiate_bound.eq_term_boundary bdry
