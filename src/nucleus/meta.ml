open Jdg_typedefs

let name m = m.meta_name

(** Meta-variables *)

let rec check_term_arguments sgn abstr args =
  (* NB: We don't actually need to instantiate the body of the abstraction,
     because we only compare the types of the arguments with the abstraction *)
  let inst_u_no_op = fun _e ?lvl u -> u in
  match (abstr, args) with
  | NotAbstract u, [] -> ()
  | Abstract _, [] -> TT_error.raise TooFewArguments
  | NotAbstract _, _::_ -> TT_error.raise TooManyArguments
  | Abstract (x, t, abstr), arg :: args ->
     let t_arg = Sanity.type_of_term sgn arg in
     if TT_alpha_equal.ty t t_arg
     then
       let abstr = TT_instantiate.abstraction inst_u_no_op arg abstr in
       check_term_arguments sgn abstr args
     else
       TT_error.raise InvalidApplication

let form_is_type_meta sgn m args =
  check_term_arguments sgn m.meta_type args ;
  TT_mk.type_meta m args

let form_is_term_meta sgn m args =
  check_term_arguments sgn m.meta_type args ;
  TT_mk.term_meta m args

let form_eq_type_meta sgn {meta_name ; meta_type} args =
  let asmp = Assumption.add_eq_type_meta meta_name meta_type Assumption.empty in
  let (lhs, rhs) =
    let inst_eq_type_boundary e0 ?lvl (lhs, rhs) =
      let lhs = TT_instantiate.ty e0 ?lvl lhs
      and rhs = TT_instantiate.ty e0 ?lvl rhs
      in (lhs, rhs)
    in
    Apply_abstraction.fully_apply_abstraction inst_eq_type_boundary sgn meta_type args
  in
  TT_mk.eq_type asmp lhs rhs

let form_eq_term_meta sgn {meta_name ; meta_type} args =
  let asmp = Assumption.add_eq_term_meta meta_name meta_type Assumption.empty in
  let (lhs, rhs, t) =
    let inst_eq_term_boundary e0 ?lvl (lhs, rhs, t) =
      let lhs = TT_instantiate.term e0 ?lvl lhs
      and rhs = TT_instantiate.term e0 ?lvl rhs
      and t = TT_instantiate.ty e0 ?lvl t
      in (lhs, rhs, t)
    in
    Apply_abstraction.fully_apply_abstraction inst_eq_term_boundary sgn meta_type args
  in
  TT_mk.eq_term asmp lhs rhs t

let meta_eta_expanded instantiate_meta form_meta abstract_meta sgn mv =
  let rec fold args = function

  | NotAbstract u ->
     TT_mk.not_abstract (form_meta sgn mv (List.rev args))

  | Abstract (x, ty, abstr) ->
     let a, abstr =
       TT_unabstract.abstraction instantiate_meta x ty abstr in
     let abstr = fold ((Form.form_is_term_atom a) :: args) abstr in
     let abstr = TT_abstract.abstraction abstract_meta a.atom_name abstr in
     TT_mk.abstract x ty abstr

  in fold [] mv.meta_type

let is_type_meta_eta_expanded =
  meta_eta_expanded
    (fun _e0 ?lvl () -> ())
    form_is_type_meta
    TT_abstract.ty

let is_term_meta_eta_expanded =
  meta_eta_expanded
    TT_instantiate.ty
    form_is_term_meta
    TT_abstract.term

let eq_type_meta_eta_expanded =
  meta_eta_expanded
    (fun e0 ?lvl (lhs, rhs) ->
       TT_instantiate.ty e0 ?lvl lhs,
       TT_instantiate.ty e0 ?lvl rhs)
    form_eq_type_meta
    TT_abstract.eq_type

let eq_term_meta_eta_expanded =
  meta_eta_expanded
    (fun e0 ?lvl (lhs, rhs, t) ->
       TT_instantiate.term e0 ?lvl lhs,
       TT_instantiate.term e0 ?lvl rhs,
       TT_instantiate.ty e0 ?lvl t)
    form_eq_term_meta
    TT_abstract.eq_term
