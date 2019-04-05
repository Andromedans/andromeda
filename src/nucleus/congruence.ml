(** Congruence rules *)

open Nucleus_types

let process_congruence_args args =

  let rec check_endpoints check t1 t2 eq =
    match t1, t2, eq with
    | NotAbstract t1, NotAbstract t2, NotAbstract eq ->
       if not (check t1 t2 eq) then Error.raise InvalidCongruence
    | Abstract ({atom_type=u1;_}, t1), Abstract ({atom_type=u2;_}, t2), Abstract ({atom_type=u';_}, eq) ->
       if Alpha_equal.is_type u1 u' || Alpha_equal.is_type u2 u' then
         check_endpoints check t1 t2 eq
       else
         Error.raise InvalidCongruence
    | _, _, _ -> Error.raise InvalidCongruence

  in
  let rec fold asmp_out lhs rhs = function

    | [] -> (asmp_out, List.rev lhs, List.rev rhs)

    | CongrIsType (t1, t2, eq) :: eqs ->
       check_endpoints
         (fun t1 t2 (EqType (_, t1', t2')) ->
            Alpha_equal.is_type t1 t1' && Alpha_equal.is_type t2 t2')
         t1 t2 eq ;
       let asmp_out = Assumption.union asmp_out (Collect_assumptions.abstraction Collect_assumptions.eq_type eq)
       in fold asmp_out (ArgumentIsType t1 :: lhs) (ArgumentIsType t2 :: rhs) eqs

    | CongrIsTerm (e1, e2, eq) :: eqs ->
       check_endpoints
         (fun e1 e2 (EqTerm (_, e1', e2', _)) ->
            Alpha_equal.is_term e1 e1' && Alpha_equal.is_term e2 e2')
         e1 e2 eq ;
       let asmp_out = Assumption.union asmp_out (Collect_assumptions.abstraction Collect_assumptions.eq_term eq)
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
  let t1 = Mk.type_constructor c lhs
  and t2 = Mk.type_constructor c rhs
  in Mk.eq_type asmp t1 t2

let congruence_term_constructor sgn c eqs =
  let (asmp, lhs, rhs) = process_congruence_args eqs in
  let e1 = Mk.term_constructor c lhs
  and e2 = Mk.term_constructor c rhs in
  let t = Sanity.type_of_term sgn e1
  in Mk.eq_term asmp e1 e2 t
