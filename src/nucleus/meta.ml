open Nucleus_types

(** Meta-variables *)

let nonce {meta_nonce=x;_} = x

let rec check_term_arguments sgn abstr args =
  (* NB: We don't actually need to instantiate the body of the abstraction,
     because we only compare the types of the arguments with the abstraction *)
  let inst_u_no_op = fun _e ?lvl u -> u in
  match (abstr, args) with
  | NotAbstract u, [] -> ()
  | Abstract _, [] -> Error.raise TooFewArguments
  | NotAbstract _, _::_ -> Error.raise TooManyArguments
  | Abstract (x, t, abstr), arg :: args ->
     let t_arg = Sanity.type_of_term sgn arg in
     if Alpha_equal.is_type t t_arg
     then
       let abstr = Instantiate_bound.abstraction inst_u_no_op arg abstr in
       check_term_arguments sgn abstr args
     else
       Error.raise InvalidApplication

let form_is_type_meta sgn m args =
  check_term_arguments sgn m.meta_type args ;
  Mk.type_meta m args

let form_is_term_meta sgn m args =
  check_term_arguments sgn m.meta_type args ;
  Mk.term_meta m args

(* let form_eq_type_meta sgn {meta_nonce; meta_type} args = *)
(*   let asmp = Assumption.add_eq_type_meta meta_nonce meta_type Assumption.empty in *)
(*   let (lhs, rhs) = *)
(*     let inst_eq_type_boundary e0 ?lvl (lhs, rhs) = *)
(*       let lhs = Instantiate_bound.is_type e0 ?lvl lhs *)
(*       and rhs = Instantiate_bound.is_type e0 ?lvl rhs *)
(*       in (lhs, rhs) *)
(*     in *)
(*     Apply_abstraction.fully_apply_abstraction inst_eq_type_boundary sgn meta_type args *)
(*   in *)
(*   Mk.eq_type asmp lhs rhs *)

(* let form_eq_term_meta sgn {meta_nonce; meta_type} args = *)
(*   let asmp = Assumption.add_eq_term_meta meta_nonce meta_type Assumption.empty in *)
(*   let (lhs, rhs, t) = *)
(*     let inst_eq_term_boundary e0 ?lvl (lhs, rhs, t) = *)
(*       let lhs = Instantiate_bound.is_term e0 ?lvl lhs *)
(*       and rhs = Instantiate_bound.is_term e0 ?lvl rhs *)
(*       and t = Instantiate_bound.is_type e0 ?lvl t *)
(*       in (lhs, rhs, t) *)
(*     in *)
(*     Apply_abstraction.fully_apply_abstraction inst_eq_term_boundary sgn meta_type args *)
(*   in *)
(*   Mk.eq_term asmp lhs rhs t *)

let form_judgement_meta sgn {meta_nonce; meta_type} args =
  let inst_meta e0 ?lvl = function
    | BoundaryIsType () ->
       BoundaryIsType ()

    | BoundaryIsTerm t ->
       (* We don't actually have to instantiate here, because we'll throw it away later *)
       let t = Instantiate_bound.is_type e0 ?lvl t in
       BoundaryIsTerm t

    | BoundaryEqType (t1, t2) ->
       let t1 = Instantiate_bound.is_type e0 ?lvl t1
       and t2 = Instantiate_bound.is_type e0 ?lvl t2 in
       BoundaryEqType (t1, t2)

    | BoundaryEqTerm (e1, e2, t) ->
       let e1 = Instantiate_bound.is_term e0 ?lvl e1
       and e2 = Instantiate_bound.is_term e0 ?lvl e2
       and t = Instantiate_bound.is_type e0 ?lvl t in
       BoundaryEqTerm (e1, e2, t)

  in
  match Apply_abstraction.fully_apply_abstraction inst_meta sgn meta_type args with

  | BoundaryIsType () ->
     begin match Boundary.as_is_type_abstraction meta_type with
     | None -> assert false
     | Some meta_type -> JudgementIsType (Mk.type_meta {meta_nonce; meta_type} args)
     end

  | BoundaryIsTerm _ ->
     begin match Boundary.as_is_term_abstraction meta_type with
     | None -> assert false
     | Some meta_type -> JudgementIsTerm (Mk.term_meta {meta_nonce; meta_type} args)
     end

  | BoundaryEqType (t1, t2) ->
     let asmp = Assumption.add_free_meta meta_nonce meta_type Assumption.empty in
     JudgementEqType (Mk.eq_type asmp t1 t2)

  | BoundaryEqTerm (e1, e2, t) ->
     let asmp = Assumption.add_free_meta meta_nonce meta_type Assumption.empty in
     JudgementEqTerm (Mk.eq_term asmp e1 e2 t)

let meta_eta_expanded' instantiate_meta form_meta abstract_meta mv =
  let rec fold args = function

    | NotAbstract u ->
       Mk.not_abstract (form_meta mv (List.rev args))

    | Abstract (x, t, abstr) ->
       let a, abstr = Unabstract.abstraction instantiate_meta x t abstr in
       let abstr = fold ((Form.form_is_term_atom a) :: args) abstr in
       let abstr = Abstract.abstraction abstract_meta a.atom_nonce abstr in
       Mk.abstract x t abstr

  in fold [] mv.meta_type

let judgement_meta_eta_expanded sgn =
  meta_eta_expanded'
    Instantiate_bound.boundary
    (form_judgement_meta sgn)
    Abstract.judgement
