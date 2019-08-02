(** Congruence rules *)

open Nucleus_types

exception Skip_argument

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

let congruence_boundaries prems args1 args2 =
  let rec fold prems_out es prems args1 args2 =
      match prems, args1, args2 with

      | [], [], [] -> List.rev prems_out

      | prem :: prems, arg1 :: args1, arg2 :: args2 ->
         begin match congruence_boundary es prem arg1 arg2 with
           | Some prem_out -> fold (prem_out :: prems_out) (arg1 :: es) prems args1 args2
           | None -> fold prems_out (arg1 :: es) prems args1 args2
         end

      | _ -> Error.raise InvalidCongruence
  in
  fold [] [] prems args1 args2


let form_rap' sgn prems constr args1 args2 =
  match congruence_boundaries prems args1 args2 with
  | [] -> RapDone (constr [])

  | bdry :: bdrys ->
     let rec rap_apply (args, bdry, bdrys) abstr =
       if not (Check.judgement_boundary_abstraction sgn abstr bdry)
       then Error.raise InvalidArgument ;
       let arg = Judgement.to_argument abstr in
       let args = arg :: args in
       match bdrys with
       | [] ->
          RapDone (constr args)

       | bdry :: bdrys ->
          RapMore (bdry, rap_apply (args, bdry, bdrys))
     in
     RapMore (bdry, rap_apply ([], bdry, bdrys))

(* Form a rule application for a congruence of two applications of the same constructor.
   We assume that [args1] and [args2] have originated from previous valid applications
   of [c] to them. *)
let form_is_term_rap sgn c args1 args2 =
  let c_prems, concl = Signature.lookup_rule c sgn in
  let t_schema =
    match concl with
      | Rule.BoundaryIsTerm t_schema -> t_schema
      | Rule.BoundaryIsType _ | Rule.BoundaryEqType _ | Rule.BoundaryEqTerm _ -> Error.raise InvalidCongruence
  in
  let constr eq_args =
    let asmp = Collect_assumptions.arguments eq_args
    and e1 = Mk.term_constructor c args1
    and e2 = Mk.term_constructor c args2
    and t = Instantiate_meta.is_type ~lvl:0 args1 t_schema in
    JudgementEqTerm (Mk.eq_term asmp e1 e2 t)
  in
  form_rap' sgn c_prems constr args1 args2

let form_is_type_rap sgn c args1 args2 =
  let c_prems, concl = Signature.lookup_rule c sgn in
  match concl with
  | Rule.BoundaryIsTerm _ | Rule.BoundaryEqType _ | Rule.BoundaryEqTerm _ -> Error.raise InvalidCongruence
  | Rule.BoundaryIsType () ->
     let constr eq_args =
       let asmp = Collect_assumptions.arguments eq_args
       and t1 = Mk.type_constructor c args1
       and t2 = Mk.type_constructor c args2 in
       JudgementEqType (Mk.eq_type asmp t1 t2)
     in
     form_rap' sgn c_prems constr args1 args2

let form_rap sgn c jdg1 jdg2 =
  match jdg1, jdg2 with

  | JudgementIsTerm e1, JudgementIsTerm e2 ->
     let rec extract_args = function
       | TermConstructor (c', args) ->
          if Ident.equal c c' then args else Error.raise InvalidCongruence
       | TermConvert (e, _, _) -> extract_args e
       | TermAtom _ | TermMeta _ -> Error.raise InvalidCongruence
       | TermBound _ -> assert false
     in
     let args1 = extract_args e1
     and args2 = extract_args e2 in
     form_is_term_rap sgn c args1 args2

  | JudgementIsType t1, JudgementIsType t2 ->
     let extract_args = function
       | TypeConstructor (c', args) ->
          if Ident.equal c c' then args else Error.raise InvalidCongruence
       | TypeMeta _ -> Error.raise InvalidCongruence
     in
     let args1 = extract_args t1
     and args2 = extract_args t2 in
     form_is_type_rap sgn c args1 args2

  | ((JudgementEqType _ | JudgementEqTerm _), _ |
     _, (JudgementEqType _ | JudgementEqTerm _) |
     JudgementIsType _, JudgementIsTerm _ |
     JudgementIsTerm _, JudgementIsType _) ->
     Error.raise InvalidCongruence
