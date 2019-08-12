(** Congruence rules *)

open Nucleus_types

exception Skip_argument

(** Given the values [es] of previous metas, a premise and two arguments
    [arg1] and [arg2] for the premise, generate an (abstracted) equation
    which equates them. If the arguments are proof irrelevant, return [None]. *)
let congruence_boundary es prem arg1 arg2 =
  let rec fold ~lvl prem arg1 arg2 =
    match prem, arg1, arg2 with

    | Rule.NotAbstract bdry, Arg_NotAbstract jdg1, Arg_NotAbstract jdg2 ->
       begin match bdry, jdg1, jdg2 with
       | Rule.BoundaryIsType (), JudgementIsType t1, JudgementIsType t2 ->
          Mk.not_abstract (BoundaryEqType (t1, t2))

       | Rule.BoundaryIsTerm t_schema, JudgementIsTerm e1, JudgementIsTerm e2 ->
          let t = Instantiate_meta.is_type ~lvl es t_schema in
          Mk.not_abstract (BoundaryEqTerm (e1, e2, t))

       | Rule.BoundaryEqType _, JudgementEqType _, JudgementEqType _
       | Rule.BoundaryEqTerm _, JudgementEqTerm _, JudgementEqTerm _ ->
          raise Skip_argument

       | _ -> Error.raise InvalidCongruence
       end

    | Rule.Abstract (x, t_schema, prem), Arg_Abstract (x1, arg1), Arg_Abstract (x2, arg2) ->
       let x = Name.prefer (Name.prefer x1 x2) x in
       let t = Instantiate_meta.is_type ~lvl es t_schema in
       let abstr = fold ~lvl:(lvl+1) prem arg1 arg2 in
       Mk.abstract x t abstr

    (* This is admittedly a bit silly. *)
    | Rule.Abstract _, Arg_NotAbstract _, Arg_NotAbstract _
    | Rule.NotAbstract _, Arg_Abstract _, Arg_NotAbstract _
    | Rule.Abstract _, Arg_Abstract _, Arg_NotAbstract _
    | Rule.NotAbstract _, Arg_NotAbstract _, Arg_Abstract _
    | Rule.Abstract _, Arg_NotAbstract _, Arg_Abstract _
    | Rule.NotAbstract _, Arg_Abstract _, Arg_Abstract _ ->
       Error.raise InvalidCongruence
  in
  try
    Some (fold ~lvl:0 prem arg1 arg2)
  with
  | Skip_argument -> None

(** Form a rule application representing the congruence rule equating the
   arguments [args1] and [args2]. *)
let form_rap' sgn form rl args1 args2 =
  let rec fold es eq_args rl args1 args2 =
    match rl, args1, args2 with

    | Rule.Conclusion concl, [], [] ->
       RapDone (form eq_args concl)

    | Rule.Premise (prem, rl), arg1 :: args1, arg2 :: args2 ->
       begin match congruence_boundary es prem arg1 arg2 with

       | None ->
          let es = arg1 :: es in
          fold es eq_args rl args1 args2

       | Some bdry ->
          let rap_apply eq_abstr =
            if not (Check.judgement_boundary_abstraction sgn eq_abstr bdry)
            then Error.raise InvalidArgument ;
            let eq_arg = Judgement.to_argument eq_abstr in
            let eq_args = eq_arg :: eq_args in
            let es = arg1 :: es in
            fold es eq_args rl args1 args2
          in
          RapMore (bdry, rap_apply)
       end

    | Rule.Conclusion _, _::_, _
    | Rule.Conclusion _, [], _::_
    | Rule.Premise _, [], _
    | Rule.Premise _, _::_, [] ->
       Error.raise InvalidCongruence
  in
  fold [] [] rl args1 args2

(* Form a rule application for a congruence of two applications of the same term constructor.
   We assume that [args1] and [args2] have originated from previous valid applications
   of [c] to them. *)
let form_is_term_rap sgn c args1 args2 =
  let form eq_args concl =
    match concl with
    | Rule.BoundaryIsTerm t_schema ->
       let asmp = Collect_assumptions.arguments eq_args
       and e1 = Mk.term_constructor c args1
       and e2 = Mk.term_constructor c args2
       and t = Instantiate_meta.is_type ~lvl:0 args1 t_schema in
       JudgementEqTerm (Mk.eq_term asmp e1 e2 t)

    | Rule.BoundaryIsType _ | Rule.BoundaryEqType _ | Rule.BoundaryEqTerm _ ->
       assert false
  in
  let rl = Signature.lookup_rule c sgn in
  form_rap' sgn form rl args1 args2

(* Form a rule application for a congruence of two applications of the same type constructor.
   We assume that [args1] and [args2] have originated from previous valid applications
   of [c] to them. *)
let form_is_type_rap sgn c args1 args2 =
  let form eq_args concl =
    match concl with
    | Rule.BoundaryIsType () ->
       let asmp = Collect_assumptions.arguments eq_args
       and t1 = Mk.type_constructor c args1
       and t2 = Mk.type_constructor c args2 in
       JudgementEqType (Mk.eq_type asmp t1 t2)

    | Rule.BoundaryIsTerm _ | Rule.BoundaryEqType _ | Rule.BoundaryEqTerm _ ->
       assert false
  in
  let rl = Signature.lookup_rule c sgn in
  form_rap' sgn form rl args1 args2

let form_rap sgn jdg1 jdg2 =
  match jdg1, jdg2 with

  | JudgementIsTerm e1, JudgementIsTerm e2 ->
     let rec extract_info = function
       | TermConstructor (c, args) -> c, args
       | TermConvert (e, _, _) -> extract_info e
       | TermAtom _ | TermMeta _ -> Error.raise InvalidCongruence
       | TermBound _ -> assert false
     in
     let c1, args1 = extract_info e1
     and c2, args2 = extract_info e2 in
     if not (Ident.equal c1 c2) then Error.raise InvalidCongruence ;
     form_is_term_rap sgn c1 args1 args2

  | JudgementIsType t1, JudgementIsType t2 ->
     let extract_info = function
       | TypeConstructor (c, args) -> c, args
       | TypeMeta _ -> Error.raise InvalidCongruence
     in
     let c1, args1 = extract_info t1
     and c2, args2 = extract_info t2 in
     if not (Ident.equal c1 c2) then Error.raise InvalidCongruence ;
     form_is_type_rap sgn c1 args1 args2

  | ((JudgementEqType _ | JudgementEqTerm _), _ |
     _, (JudgementEqType _ | JudgementEqTerm _) |
     JudgementIsType _, JudgementIsTerm _ |
     JudgementIsTerm _, JudgementIsType _) ->
     Error.raise InvalidCongruence
