open Nucleus_types

let atom_name {atom_nonce=x;_} = Nonce.name x

(** Destructors *)

let invert_is_term sgn = function

  | TermAtom a -> Stump_TermAtom a

  | TermBound _ -> assert false

  | TermConstructor (c, args) ->
     Stump_TermConstructor (c, args)

  | TermMeta (mv, args) ->
     Stump_TermMeta (mv, args)

  | TermConvert (e, asmp, t) ->
     let t' = Sanity.natural_type sgn e in
     let eq = Mk.eq_type asmp t' t in
     Stump_TermConvert (e, eq)

let invert_is_type = function
  | TypeConstructor (c, args) ->
     Stump_TypeConstructor (c, args)

  | TypeMeta (mv, args) -> Stump_TypeMeta (mv, args)

let invert_eq_type (EqType (asmp, t1, t2)) = Stump_EqType (asmp, t1, t2)

let invert_eq_term (EqTerm (asmp, e1, e2, t)) = Stump_EqTerm (asmp, e1, e2, t)

let as_not_abstract = function
  | Abstract _ -> None
  | NotAbstract v -> Some v

let as_abstract = function
  | Abstract (atm, abstr) -> Some (atm, abstr)
  | NotAbstract _ -> None

let invert_abstraction ?name inst_v = function
  | Abstract ({atom_nonce=x; atom_type=t}, abstr) ->
     let x = (match name with None -> Nonce.name x | Some y -> y) in
     let a = Mk.fresh_atom x t in
     let abstr = Instantiate_bound.abstraction inst_v (Mk.atom a) abstr in
     Stump_Abstract (a, abstr)
  | NotAbstract v -> Stump_NotAbstract v

(* We often need to jointly invert two abstractions at the same time, e.g.,
   when type-checking an abstracted judgement against an abstracted boundary.
   The following function does this in a reasonable manner by inverting two
   abstractions with the same atom. *)
let invert_abstractions ?name inst_u inst_v abstr_u abstr_v =
  match abstr_u, abstr_v with

  | NotAbstract u, NotAbstract v -> Some (Stumps_NotAbstract (u, v))

  | Abstract ({atom_nonce=x_u; atom_type=t_u}, abstr_u),
    Abstract ({atom_nonce=x_v; atom_type=t_v}, abstr_v) ->
     if not (Alpha_equal.is_type t_u t_v) then
       None
     else
       let x = (match name with None -> Nonce.name x_u | Some y -> y) in
       let a = Mk.fresh_atom x t_u in
       let a' = Mk.atom a in
       let abstr_u = Instantiate_bound.abstraction inst_u a' abstr_u
       and abstr_v = Instantiate_bound.abstraction inst_v a' abstr_v in
       Some (Stumps_Abstract (a, abstr_u, abstr_v))

  | Abstract _, NotAbstract _
  | NotAbstract _, Abstract _ -> None

let invert_is_type_abstraction ?name t =
  invert_abstraction ?name Instantiate_bound.is_type t

let invert_is_term_abstraction ?name e =
  invert_abstraction ?name Instantiate_bound.is_term e

let invert_eq_type_abstraction ?name eq =
  invert_abstraction ?name Instantiate_bound.eq_type eq

let invert_eq_term_abstraction ?name eq =
  invert_abstraction ?name Instantiate_bound.eq_term eq

let invert_judgement_abstraction ?name jdg =
  invert_abstraction ?name Instantiate_bound.judgement jdg

let invert_eq_term_boundary bdry = bdry

let invert_is_type_boundary_abstraction ?name bdry =
  invert_abstraction ?name Instantiate_bound.is_type_boundary bdry

let invert_is_term_boundary_abstraction ?name bdry =
  invert_abstraction ?name Instantiate_bound.is_term_boundary bdry

let invert_eq_type_boundary_abstraction ?name bdry =
  invert_abstraction ?name Instantiate_bound.eq_type_boundary bdry

let invert_eq_term_boundary_abstraction ?name bdry =
  invert_abstraction ?name Instantiate_bound.eq_term_boundary bdry

let invert_boundary_abstraction ?name jdg =
  invert_abstraction ?name Instantiate_bound.boundary jdg
