open Nucleus_types

let type_of_atom {atom_type=t;_} = t


(** Apply [abstr] to a list of terms of length equal to the abstraction
    level of [abstr]. Do not verify the terms to be substituted match the
    types on the abstraction. Use with care! *)
let fully_apply_abstraction_no_checks inst_u abstr args =
  let rec fold es abstr args =
    match abstr, args with
    | NotAbstract u, [] -> inst_u es u
    | Abstract (_, _, abstr), e :: args -> fold (e :: es) abstr args
    | Abstract _, [] -> Error.raise TooFewArguments
    | NotAbstract _, _::_ -> Error.raise TooManyArguments
  in
  fold [] abstr args

(** [type_of_term sgn e] gives a type judgment [t], where [t] is the type of [e].
    Note that [t] itself gives no evidence that [e] actually has type [t].
    However, the assumptions of [e] are sufficient to show that [e] has
    type [t].  *)
let type_of_term sgn = function
  | TermAtom {atom_type=t; _} -> t

  | TermBoundVar k ->
     (* We should never get here. If ever we need to compute the type of a
        term with bound variables, then we should have unabstracted the term
        beforehand, and asked about the type of the unabstracted version. *)
     assert false

  | TermConstructor (c, args) ->
     (* we need not re-check that the premises match the arguments because
        we are computing the type of a term that was previously determined
        to be valid. *)
     let rec fold inds rl args =
       match rl, args with

       | Premise (_, rl), arg :: args -> fold (arg :: inds) rl args

       | Conclusion (BoundaryIsTerm t_schema), [] ->
          Instantiate_meta.is_type ~lvl:0 inds t_schema

       | Conclusion (BoundaryIsType _ | BoundaryEqType _ | BoundaryEqTerm _), []
       | Premise _, []
       | Conclusion _, _::_ ->
          assert false
     in
     let rl = Signature.lookup_rule c sgn in
     fold [] rl args

  | TermMeta (MetaBound _, _) ->
     (* We should never get here. If ever we need to compute the type of a term with a
        bound meta-variables, then we should have applied the term. *)
     assert false

  | TermMeta (MetaFree {meta_boundary;_}, args) ->
     begin match Boundary.as_is_term_abstraction meta_boundary with
     | None -> assert false
     | Some bdry -> fully_apply_abstraction_no_checks (Instantiate_bound.is_type_fully ?lvl:None) bdry args
     end

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
     let t_abstr = Abstract.abstraction Abstract.is_type a.atom_nonce t_abstr in
     Mk.abstract x t t_abstr

let rec abstracted_judgement_with_boundary sgn abstr_jdg = 
  match abstr_jdg with 
    | NotAbstract (JudgementIsTerm jdg as jdg') -> 
      Mk.not_abstract (jdg', BoundaryIsTerm (type_of_term sgn jdg))

    | NotAbstract (JudgementIsType jdg as jdg')-> 
      Mk.not_abstract (jdg', BoundaryIsType ())

    | NotAbstract (JudgementEqType (EqType (asmp, t1, t2)) as jdg') -> 
      Mk.not_abstract (jdg', BoundaryEqType (t1,t2))

    | NotAbstract (JudgementEqTerm (EqTerm (asmp, e1, e2, t)) as jdg')-> 
      Mk.not_abstract (jdg', BoundaryEqTerm (e1, e2, t)) 

    | Abstract (x, t, abstr) -> 
      let a, abstr = Unabstract.abstraction Instantiate_bound.judgement x t abstr in
      let abstr_pair = abstracted_judgement_with_boundary sgn abstr in
      let abstr_pair = Abstract.judgement_with_boundary_abstraction a abstr_pair in
      Mk.abstract x t abstr_pair

(** [natural_type sgn e] gives the judgment that the natural type [t] of [e] is derivable.
    We maintain the invariant that no further assumptions are needed (apart from those
    already present in [e]) to derive that [e] actually has type [t]. *)
let natural_type sgn = function
  | (TermAtom _ | TermBoundVar _ | TermConstructor _ | TermMeta _) as e ->
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

let boundary_eq_type_abstraction abstr =
  (* We may drop the assumption set of the argument because that assumption set
     is needed to inhabit the equality, not to form its boundary. The boundary carries
     its own assumptions. *)
  boundary_abstraction (fun (EqType (_, t, u)) -> (t, u)) abstr

let boundary_eq_term_abstraction abstr =
  boundary_abstraction (fun (EqTerm (_, a, b, t)) -> (a, b, t)) abstr
