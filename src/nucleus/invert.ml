open Jdg_typedefs

(** Destructors *)

let invert_argument = function
  | ArgumentIsTerm abstr -> ArgumentIsTerm abstr
  | ArgumentIsType abstr -> ArgumentIsType abstr
  | ArgumentEqType abstr -> ArgumentEqType abstr
  | ArgumentEqTerm abstr -> ArgumentEqTerm abstr

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
     let eq = TT_mk.eq_type asmp t' t in
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

let invert_abstraction ?atom_name inst_v = function
  | Abstract (x, t, abstr) ->
     let x = (match atom_name with None -> x | Some y -> y) in
     let a = TT_mk.fresh_atom x t in
     let abstr = TT_instantiate.abstraction inst_v (TT_mk.atom a) abstr in
     Stump_Abstract (a, abstr)
  | NotAbstract v -> Stump_NotAbstract v

let invert_is_type_abstraction ?atom_name t =
  invert_abstraction ?atom_name TT_instantiate.ty t

let invert_is_term_abstraction ?atom_name e =
  invert_abstraction ?atom_name TT_instantiate.term e

let invert_eq_type_abstraction ?atom_name eq =
  invert_abstraction ?atom_name TT_instantiate.eq_type eq

let invert_eq_term_abstraction ?atom_name eq =
  invert_abstraction ?atom_name TT_instantiate.eq_term eq

let atom_name {atom_name=n;_} = n
