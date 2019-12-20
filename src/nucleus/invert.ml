open Nucleus_types

let atom_name {atom_nonce=x;_} = Nonce.name x

(** Destructors *)

let rec invert_argument ~lvl es prem arg =
  match prem, arg with

  | NotAbstract _, Arg_NotAbstract jdg ->
     NotAbstract jdg

  | Abstract (x, t_schema, prem), Arg_Abstract (y, arg) ->
     let y = Name.prefer y x in
     let t = Instantiate_meta.is_type ~lvl es t_schema in
     let abstr = invert_argument ~lvl:(lvl+1) es prem arg in
     Mk.abstract y t abstr

  | (NotAbstract _, Arg_Abstract _ | Abstract _, Arg_NotAbstract _) ->
     assert false

let invert_arguments rl args =
  let rec fold es abstrs rl args =
    match rl, args with
    | Conclusion _, [] -> List.rev abstrs

    | Premise ({meta_boundary=prem;_}, rl), arg :: args ->
       let abstr = invert_argument ~lvl:0 es prem arg in
       fold (arg :: es) (abstr :: abstrs) rl args

    | Conclusion _, _::_
    | Premise _, [] ->
       assert false
  in
  fold [] [] rl args

let invert_is_term sgn = function

  | TermAtom a -> Stump_TermAtom a

  | TermBoundVar _ -> assert false

  | TermConstructor (c, args) ->
     let rl = Signature.lookup_rule c sgn in
     let abstrs = invert_arguments rl args in
     Stump_TermConstructor (c, abstrs)

  | TermMeta (MetaBound _, _) ->
     assert false

  | TermMeta (MetaFree mv, args) ->
     Stump_TermMeta (mv, args)

  | TermConvert (e, asmp, t) ->
     let t' = Sanity.natural_type sgn e in
     let eq = Mk.eq_type asmp t' t in
     Stump_TermConvert (e, eq)

let invert_is_type sgn = function
  | TypeConstructor (c, args) ->
     let rl = Signature.lookup_rule c sgn in
     let abstrs = invert_arguments rl args in
     Stump_TypeConstructor (c, abstrs)

  | TypeMeta (MetaBound _, _) ->
     assert false

  | TypeMeta (MetaFree mv, args) ->
     Stump_TypeMeta (mv, args)

let invert_eq_type (EqType (asmp, t1, t2)) = Stump_EqType (asmp, t1, t2)

let invert_eq_term sgn (EqTerm (asmp, e1, e2, t)) =
  let t1 = Sanity.type_of_term sgn e1
  and t2 = Sanity.type_of_term sgn e2 in
  let e1 = if Alpha_equal.is_type t1 t then e1 else Mk.term_convert e1 asmp t
  and e2 = if Alpha_equal.is_type t2 t then e2 else Mk.term_convert e2 asmp t
  in
  Stump_EqTerm (asmp, e1, e2, t)

let as_not_abstract = function
  | Abstract _ -> None
  | NotAbstract v -> Some v

let invert_abstraction ?name inst_v = function
  | Abstract (x, t, abstr) ->
     let x = (match name with None -> x | Some y -> y) in
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

  | Abstract (x_u, t_u, abstr_u),
    Abstract (x_v, t_v, abstr_v) ->
     if not (Alpha_equal.is_type t_u t_v) then
       None
     else
       let x = (match name with None -> x_u | Some y -> y) in
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
