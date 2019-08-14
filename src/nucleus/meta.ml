open Nucleus_types

(** Meta-variables *)

let form_meta x abstr =
  let n, mv = Mk.fresh_meta x abstr in
  let rec fold k args = function
    | NotAbstract bdry ->

       begin match bdry with
       | BoundaryIsType () ->
          Mk.not_abstract (JudgementIsType (Mk.type_meta mv args))

       | BoundaryIsTerm _ ->
          Mk.not_abstract (JudgementIsTerm (Mk.term_meta mv args))

       | BoundaryEqType (t1, t2) ->
          Mk.not_abstract (JudgementEqType (Mk.eq_type Assumption.empty t1 t2))

       | BoundaryEqTerm (e1, e2, t) ->
          Mk.not_abstract (JudgementEqTerm (Mk.eq_term Assumption.empty e1 e2 t))
       end

    | Abstract (x, t, abstr) ->
       let arg = Mk.bound k in
       let abstr = fold (k+1) (arg :: args) abstr in
       Mk.abstract x t abstr
  in
  (* We always return the nonce, even for thought equality judgements do not really
     yield meta-variables. The nonces are there so that correct de Bruijn indices are
     computed when the a rule is formed. It just so happens that the nonces corresponding
     to the equality premises never get referenced. The alternative would be to have
     optional onces, and optional binding, and that's really error-prone, we tried. *)
  n, fold 0 [] abstr
