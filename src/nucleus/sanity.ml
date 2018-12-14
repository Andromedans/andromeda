open Nucleus_types

let type_of_atom {atom_type=t;_} = t

(** [type_of_term sgn e] gives a type judgment [t], where [t] is the type of [e].
    Note that [t] itself gives no evidence that [e] actually has type [t].
    However, the assumptions of [e] are sufficient to show that [e] has
    type [t].  *)
let type_of_term sgn = function
  | TermAtom {atom_type=t; _} -> t

  | TermBound k ->
     (* We should never get here. If ever we need to compute the type of a
        term with bound variables, then we should have unabstracted the term
        beforehand, and asked about the type of the unabstracted version. *)
     assert false

  | TermConstructor (c, args) ->
     let (_premises, t_schema) = Signature.lookup_rule_is_term c sgn in
     (* we need not re-check that the premises match the arguments because
        we are computing the type of a term that was previously determined
        to be valid. *)
     let inds = Indices.of_list args in
     Instantiate_meta.is_type ~lvl:0 inds t_schema

  | TermMeta ({meta_type;_}, args) ->
     Instantiate_meta.fully_apply_abstraction_no_typechecks
       (Instantiate_bound.is_type_fully ?lvl:None) meta_type args

  | TermConvert (e, _, t) -> t


let type_at_abstraction = function
  | NotAbstract _ -> None
  | Abstract (_, t, _) -> Some t

let rec type_of_term_abstraction sgn = function
  | NotAbstract e ->
     let t = type_of_term sgn e in
     Mk.not_abstract t

  | Abstract (x, t, abstr) ->
     let a, abstr = Unabstract.abstraction Instantiate_bound.is_term x t abstr in
     let t_abstr = type_of_term_abstraction sgn abstr in
     let t_abstr = Abstract.abstraction Abstract.is_type a.atom_name t_abstr in
     Mk.abstract x t t_abstr

(** [natural_type sgn e] gives the judgment that the natural type [t] of [e] is derivable.
    We maintain the invariant that no further assumptions are needed (apart from those
    already present in [e]) to derive that [e] actually has type [t]. *)
let natural_type sgn = function
  | (TermAtom _ | TermBound _ | TermConstructor _ | TermMeta _) as e ->
     type_of_term sgn e

  | TermConvert (e, _, _) -> type_of_term sgn e

let natural_type_eq sgn e =
  let natural = natural_type sgn e
  and given = type_of_term sgn e in
  (* XXX should the assumptions here be empty, or the assumptions of [e] ? If
     we derived [e : given] via a conversion, eg

     ⊢ e' : natural   x : False ⊢ natural == given
     --------------------------------------------conv
     x  : False ⊢ e : given

     then we should include the assumptions of [e], i.e. [x], in the assumptions
     of [natural == given]

     NB: We should actually look into [e] and if it's a conversion, grab that
     assumption set.
  *)
  Mk.eq_type Assumption.empty natural given

let rec boundary_abstraction boundary_u = function
  | NotAbstract u -> Mk.not_abstract (boundary_u u)
  | Abstract (x, t, abstr) ->
     let b = boundary_abstraction boundary_u abstr in
     Mk.abstract x t b

let boundary_is_type_abstraction abstr =
  boundary_abstraction (fun _ -> ()) abstr

let boundary_is_term_abstraction sgn abstr =
  (* NB: this is _not_ like the others as it actually computes the type of a term *)
  type_of_term_abstraction sgn abstr

let boundary_eq_type_abstraction abstr = abstr

let boundary_eq_term_abstraction abstr = abstr
