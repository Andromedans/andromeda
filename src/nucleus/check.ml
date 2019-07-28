open Nucleus_types

(** Checking judgements against their boundaries *)

let is_type_boundary abstr bdry = true

let is_term_boundary sgn e t =
  Alpha_equal.is_type (Sanity.type_of_term sgn e) t

let eq_type_boundary (EqType (_asmp, t1, t2)) (u1, u2) =
  Alpha_equal.is_type t1 u1 && Alpha_equal.is_type t2 u2

let eq_term_boundary (EqTerm (_asmp, a, b, t)) (a', b', t') =
  Alpha_equal.is_type t t' && Alpha_equal.is_term a a' && Alpha_equal.is_term b b'

let judgement_boundary sgn jdg bdry =
  match bdry with
    | BoundaryIsType bdry ->
       begin match jdg with
       | JudgementIsType jdg -> is_type_boundary jdg bdry
       | JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _ -> false
       end

    | BoundaryIsTerm bdry ->
       begin match jdg with
       | JudgementIsTerm jdg -> is_term_boundary sgn jdg bdry
       | JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _ -> false
       end

    | BoundaryEqType bdry ->
       begin match jdg with
       | JudgementEqType jdg -> eq_type_boundary jdg bdry
       | JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _ -> false
       end

    | BoundaryEqTerm bdry ->
       begin match jdg with
       | JudgementEqTerm jdg -> eq_term_boundary jdg bdry
       | JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _ -> false
       end

let rec judgement_boundary_abstraction sgn abstr_jdg abstr_bdry =
  match Invert.invert_abstractions Instantiate_bound.judgement Instantiate_bound.boundary abstr_jdg abstr_bdry with
  | None -> false

  | Some (Stumps_NotAbstract (jdg, bdry)) ->
     judgement_boundary sgn jdg bdry

  | Some (Stumps_Abstract (_atm, abstr_jdg, abstr_bdry)) ->
     judgement_boundary_abstraction sgn abstr_jdg abstr_bdry
