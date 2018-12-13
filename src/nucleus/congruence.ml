(** Congruence rules *)

open Jdg_typedefs

let process_congruence_args args =

  let rec check_endpoints check t1 t2 eq =
    match t1, t2, eq with
    | NotAbstract t1, NotAbstract t2, NotAbstract eq ->
       if not (check t1 t2 eq) then TT_error.raise InvalidCongruence
    | Abstract (_x1, u1, t1), Abstract (_x2, u2, t2), Abstract (_x', u', eq) ->
       if TT_alpha_equal.ty u1 u' || TT_alpha_equal.ty u2 u' then
         check_endpoints check t1 t2 eq
       else
         TT_error.raise InvalidCongruence
    | _, _, _ -> TT_error.raise InvalidCongruence

  in
  let rec fold asmp_out lhs rhs = function

    | [] -> (asmp_out, List.rev lhs, List.rev rhs)

    | CongrIsType (t1, t2, eq) :: eqs ->
       check_endpoints
         (fun t1 t2 (EqType (_, t1', t2')) ->
           TT_alpha_equal.ty t1 t1' && TT_alpha_equal.ty t2 t2')
         t1 t2 eq ;
       let asmp_out = Assumption.union asmp_out (TT_assumption.abstraction TT_assumption.eq_type eq)
       in fold asmp_out (ArgumentIsType t1 :: lhs) (ArgumentIsType t2 :: rhs) eqs

    | CongrIsTerm (e1, e2, eq) :: eqs ->
       check_endpoints
         (fun e1 e2 (EqTerm (_, e1', e2', _)) ->
           TT_alpha_equal.term e1 e1' && TT_alpha_equal.term e2 e2')
         e1 e2 eq ;
       let asmp_out = Assumption.union asmp_out (TT_assumption.abstraction TT_assumption.eq_term eq)
       in fold asmp_out (ArgumentIsTerm e1 :: lhs) (ArgumentIsTerm e2 :: rhs) eqs

    | CongrEqType (eq1, eq2) :: eqs ->
       let l = ArgumentEqType eq1
       and r = ArgumentEqType eq2
       in fold asmp_out (l :: lhs) (r :: rhs) eqs

    | CongrEqTerm (eq1, eq2) :: eqs ->
       let l = ArgumentEqTerm eq1
       and r = ArgumentEqTerm eq2
       in fold asmp_out (l :: lhs) (r :: rhs) eqs

  in fold Assumption.empty [] [] args


let congruence_type_constructor sgn c eqs =
  let (asmp, lhs, rhs) = process_congruence_args eqs in
  let t1 = Form.form_is_type sgn c lhs
  and t2 = Form.form_is_type sgn c rhs
  in TT_mk.eq_type asmp t1 t2

let congruence_term_constructor sgn c eqs =
  let (asmp, lhs, rhs) = process_congruence_args eqs in
  let e1 = Form.form_is_term sgn c lhs
  and e2 = Form.form_is_term sgn c rhs in
  let t = Sanity.type_of_term sgn e1
  in TT_mk.eq_term asmp e1 e2 t
