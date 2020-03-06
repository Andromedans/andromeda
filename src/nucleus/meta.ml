open Nucleus_types

(** Meta-variables *)

(** Compare two meta-variables for equality *)
let equal {meta_nonce=n1;_} {meta_nonce=n2;_} = Nonce.equal n1 n2

(** Create a fresh meta-variable, return it and its fully exapnded form. *)
let form_meta x abstr =
  let mv = Mk.free_meta x abstr in
  let rec fold k args = function
    | NotAbstract bdry ->

       begin match bdry with
       | BoundaryIsType () ->
          Mk.not_abstract (JudgementIsType (Mk.type_meta (MetaFree mv) args))

       | BoundaryIsTerm _ ->
          Mk.not_abstract (JudgementIsTerm (Mk.term_meta (MetaFree mv) args))

       | BoundaryEqType (t1, t2) ->
          Mk.not_abstract (JudgementEqType (Mk.eq_type_meta (MetaFree mv) t1 t2))

       | BoundaryEqTerm (e1, e2, t) ->
          Mk.not_abstract (JudgementEqTerm (Mk.eq_term_meta (MetaFree mv) e1 e2 t))
       end

    | Abstract (x, t, abstr) ->
       let arg = Mk.bound k in
       let abstr = fold (k+1) (arg :: args) abstr in
       Mk.abstract x t abstr
  in
  mv, fold 0 [] abstr
