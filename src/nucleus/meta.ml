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
  | Abstract ({atom_nonce=x; atom_type=t}, abstr), arg :: args ->
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

let form_eq_type_meta sgn {meta_nonce; meta_type} args =
  let asmp = Assumption.add_eq_type_meta meta_nonce meta_type Assumption.empty in
  let (lhs, rhs) =
    let inst_eq_type_boundary e0 ?lvl (lhs, rhs) =
      let lhs = Instantiate_bound.is_type e0 ?lvl lhs
      and rhs = Instantiate_bound.is_type e0 ?lvl rhs
      in (lhs, rhs)
    in
    Apply_abstraction.fully_apply_abstraction inst_eq_type_boundary sgn meta_type args
  in
  Mk.eq_type asmp lhs rhs

let form_eq_term_meta sgn {meta_nonce; meta_type} args =
  let asmp = Assumption.add_eq_term_meta meta_nonce meta_type Assumption.empty in
  let (lhs, rhs, t) =
    let inst_eq_term_boundary e0 ?lvl (lhs, rhs, t) =
      let lhs = Instantiate_bound.is_term e0 ?lvl lhs
      and rhs = Instantiate_bound.is_term e0 ?lvl rhs
      and t = Instantiate_bound.is_type e0 ?lvl t
      in (lhs, rhs, t)
    in
    Apply_abstraction.fully_apply_abstraction inst_eq_term_boundary sgn meta_type args
  in
  Mk.eq_term asmp lhs rhs t

let form_judgement_meta sgn mv args = failwith "form_judgement_meta not implemented"

let meta_eta_expanded' instantiate_meta form_meta abstract_meta mv =
  let rec fold args = function

    | NotAbstract u ->
       Mk.not_abstract (form_meta mv (List.rev args))

    | Abstract (atm, abstr) ->
       let a, abstr =
         Unabstract.abstraction instantiate_meta (Nonce.name atm.atom_nonce) atm.atom_type abstr in
       let abstr = fold ((Form.form_is_term_atom a) :: args) abstr in
       let abstr = Abstract.abstraction abstract_meta a.atom_nonce abstr in
       Mk.abstract atm abstr

  in fold [] mv.meta_type

let is_type_meta_eta_expanded sgn =
  meta_eta_expanded'
    (fun _e0 ?lvl () -> ())
    (form_is_type_meta sgn)
    Abstract.is_type

let is_term_meta_eta_expanded sgn =
  meta_eta_expanded'
    Instantiate_bound.is_type
    (form_is_term_meta sgn)
    Abstract.is_term

let eq_type_meta_eta_expanded sgn =
  meta_eta_expanded'
    (fun e0 ?lvl (lhs, rhs) ->
       Instantiate_bound.is_type e0 ?lvl lhs,
       Instantiate_bound.is_type e0 ?lvl rhs)
    (form_eq_type_meta sgn)
    Abstract.eq_type

let eq_term_meta_eta_expanded sgn =
  meta_eta_expanded'
    (fun e0 ?lvl (lhs, rhs, t) ->
       Instantiate_bound.is_term e0 ?lvl lhs,
       Instantiate_bound.is_term e0 ?lvl rhs,
       Instantiate_bound.is_type e0 ?lvl t)
    (form_eq_term_meta sgn)
    Abstract.eq_term

let judgement_meta_eta_expanded sgn =
  meta_eta_expanded'
    Instantiate_bound.boundary
    (form_judgement_meta sgn)
    Abstract.judgement
