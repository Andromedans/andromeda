(** Congruence rules *)

open Nucleus_types

exception Skip_argument

(** Given the values [es] of previous metas, a premise and two arguments
    [arg1] and [arg2] for the premise, generate an (abstracted) equation
    which equates them. If the arguments are proof irrelevant, return [None]. *)
let congruence_boundary es prem arg1 arg2 =
  let rec fold ~lvl prem arg1 arg2 =
    match prem, arg1, arg2 with

    | NotAbstract bdry, Arg_NotAbstract jdg1, Arg_NotAbstract jdg2 ->
       begin match bdry, jdg1, jdg2 with
       | BoundaryIsType (), JudgementIsType t1, JudgementIsType t2 ->
          Mk.not_abstract (BoundaryEqType (t1, t2))

       | BoundaryIsTerm t_schema, JudgementIsTerm e1, JudgementIsTerm e2 ->
          let t = Instantiate_meta.is_type ~lvl es t_schema in
          Mk.not_abstract (BoundaryEqTerm (e1, e2, t))

       | BoundaryEqType _, JudgementEqType _, JudgementEqType _
       | BoundaryEqTerm _, JudgementEqTerm _, JudgementEqTerm _ ->
          raise Skip_argument

       | _ -> Error.raise InvalidCongruence
       end

    | Abstract (x, t_schema, prem), Arg_Abstract (x1, arg1), Arg_Abstract (x2, arg2) ->
       let x = Name.prefer (Name.prefer x1 x2) x in
       let t = Instantiate_meta.is_type ~lvl es t_schema in
       let abstr = fold ~lvl:(lvl+1) prem arg1 arg2 in
       Mk.abstract x t abstr

    (* This is admittedly a bit silly. *)
    | Abstract _, Arg_NotAbstract _, Arg_NotAbstract _
    | NotAbstract _, Arg_Abstract _, Arg_NotAbstract _
    | Abstract _, Arg_Abstract _, Arg_NotAbstract _
    | NotAbstract _, Arg_NotAbstract _, Arg_Abstract _
    | Abstract _, Arg_NotAbstract _, Arg_Abstract _
    | NotAbstract _, Arg_Abstract _, Arg_Abstract _ ->
       Error.raise InvalidCongruence
  in
  try
    Some (fold ~lvl:0 prem arg1 arg2)
  with
  | Skip_argument -> None

(** Form a rule application representing the congruence rule derived from the given
    rule [rl] applied to [args1] and [args2]. *)
let form_rule_rap sgn form rl args1 args2 =
  let rec fold es eq_args rl args1 args2 =
    match rl, args1, args2 with

    | Conclusion concl, [], [] ->
       RapDone (form eq_args concl)

    | Premise ({meta_boundary=prem;_}, rl), arg1 :: args1, arg2 :: args2 ->
       begin match congruence_boundary es prem arg1 arg2 with

       | None ->
          let es = arg1 :: es in
          fold es eq_args rl args1 args2

       | Some bdry ->
          let rap_apply eq_abstr =
            if not (Check.judgement_boundary_abstraction sgn eq_abstr bdry)
            then Error.raise InvalidArgument ;
            let eq_arg = Coerce.to_argument eq_abstr in
            let eq_args = eq_arg :: eq_args in
            let es = arg1 :: es in
            fold es eq_args rl args1 args2
          in
          RapMore (bdry, rap_apply)
       end

    | Conclusion _, _::_, _
    | Conclusion _, [], _::_
    | Premise _, [], _
    | Premise _, _::_, [] ->
       Error.raise InvalidCongruence
  in
  fold [] [] rl args1 args2

let form_meta_rap form abstr args1 args2 =
  let rec fold es eq_args abstr args1 args2 =
    match abstr, args1, args2 with

    | NotAbstract bdry, [], [] ->
       RapDone (form eq_args bdry)

    | Abstract (_, t', abstr), arg1 :: args1, arg2 :: args2 ->
       let t = Instantiate_bound.is_type_fully es t' in
       let bdry = (arg1, arg2, t) in
       let rap_apply = function
         | NotAbstract (JudgementEqTerm eq) ->
            if not (Check.eq_term_boundary eq bdry) then Error.raise InvalidCongruence ;
            let eq_arg = Arg_NotAbstract (JudgementEqTerm eq) in
            let eq_args = eq_arg :: eq_args in
            let es = arg1 :: es in
            fold es eq_args abstr args1 args2

         | NotAbstract (JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _)
         | Abstract _ ->
            Error.raise InvalidCongruence
       in
       RapMore (NotAbstract (BoundaryEqTerm bdry), rap_apply)

    | NotAbstract _, _::_, _
    | NotAbstract _, _, _::_
    | Abstract _, [], _
    | Abstract _, _, [] ->
       Error.raise InvalidCongruence
  in
  fold [] [] abstr args1 args2

(* Form a rule application for a congruence of two applications of the same term constructor.
   We assume that [args1] and [args2] have originated from previous valid applications
   of [c] to them. *)
let form_is_term_rap sgn c args1 args2 =
  let form eq_args concl =
    match concl with
    | BoundaryIsTerm t_schema ->
       let asmp = Collect_assumptions.arguments eq_args
       and e1 = Mk.term_constructor c args1
       and e2 = Mk.term_constructor c args2
       and t = Instantiate_meta.is_type ~lvl:0 (List.rev args1) t_schema in
       JudgementEqTerm (Mk.eq_term asmp e1 e2 t)

    | BoundaryIsType _ | BoundaryEqType _ | BoundaryEqTerm _ ->
       assert false
  in
  let rl = Signature.lookup_rule c sgn in
  form_rule_rap sgn form rl args1 args2

(* Form a rule application for a congruence of two applications of the same type constructor.
   We assume that [args1] and [args2] have originated from previous valid applications
   of [c] to them. *)
let form_is_type_rap sgn c args1 args2 =
  let form eq_args concl =
    match concl with
    | BoundaryIsType () ->
       let asmp = Collect_assumptions.arguments eq_args
       and t1 = Mk.type_constructor c args1
       and t2 = Mk.type_constructor c args2 in
       JudgementEqType (Mk.eq_type asmp t1 t2)

    | BoundaryIsTerm _ | BoundaryEqType _ | BoundaryEqTerm _ ->
       assert false
  in
  let rl = Signature.lookup_rule c sgn in
  form_rule_rap sgn form rl args1 args2

let form_judgement sgn jdg1 jdg2 =
  match jdg1, jdg2 with

  | JudgementIsTerm e1, JudgementIsTerm e2 ->
     let rec form = function
       | TermConvert (e1, _, _), e2 -> form (e1, e2)

       | e1, TermConvert (e2, _, _) -> form (e1, e2)

       | TermConstructor (c1, args1), TermConstructor (c2, args2) ->
          if not (Ident.equal c1 c2) then Error.raise InvalidCongruence ;
          form_is_term_rap sgn c1 args1 args2

       | (TermMeta (MetaFree {meta_nonce=n1; meta_boundary}, args1) as e1), (TermMeta (MetaFree {meta_nonce=n2;_}, args2) as e2) ->
          let abstr = (match Boundary.as_is_term_abstraction meta_boundary with Some abstr -> abstr | None -> assert false) in
          if not (Nonce.equal n1 n2) then Error.raise InvalidCongruence ;
          form_meta_rap
          (fun eq_args t' ->
            let t = Instantiate_bound.is_type_fully (Indices.of_list args1) t' in
            let asmp = Collect_assumptions.arguments eq_args in
            JudgementEqTerm (Mk.eq_term asmp e1 e2 t))
          abstr
          args1 args2


       | TermAtom x as e1, TermAtom y ->
          if Nonce.equal x.atom_nonce y.atom_nonce then
            let eq = Form.reflexivity_term sgn e1 in
            RapDone (JudgementEqTerm eq)
          else
            Error.raise InvalidCongruence

       | TermMeta _, (TermConstructor _ | TermAtom _)
       | TermConstructor _, (TermMeta _ | TermAtom _)
       | TermAtom _, (TermMeta _ | TermConstructor _) ->
          Error.raise InvalidCongruence

       | TermMeta (MetaBound _, _), _ | _, TermMeta (MetaBound _, _)
       | TermBoundVar _, _ | _, TermBoundVar _ -> assert false
     in
     form (e1, e2)

  | JudgementIsType t1, JudgementIsType t2 ->
     begin match t1, t2 with
     | TypeConstructor (c1, args1), TypeConstructor (c2, args2) ->
        if not (Ident.equal c1 c2) then Error.raise InvalidCongruence ;
        form_is_type_rap sgn c1 args1 args2

     | TypeMeta (MetaFree {meta_nonce=n1; meta_boundary}, args1), TypeMeta (MetaFree {meta_nonce=n2;_}, args2) ->
        let abstr = (match Boundary.as_is_type_abstraction meta_boundary with Some abstr -> abstr | None -> assert false) in
        if not (Nonce.equal n1 n2) then Error.raise InvalidCongruence ;
        form_meta_rap
          (fun eq_args () ->
            let asmp = Collect_assumptions.arguments eq_args in
            JudgementEqType (Mk.eq_type asmp t1 t2))
          abstr
          args1 args2

     | TypeMeta (MetaBound _, _), _ | _, TypeMeta (MetaBound _, _)
     | TypeConstructor _, TypeMeta _
     | TypeMeta _, TypeConstructor _ ->
        Error.raise InvalidCongruence
     end

  | (JudgementEqType _ | JudgementEqTerm _), _
  | _, (JudgementEqType _ | JudgementEqTerm _)
  | JudgementIsType _, JudgementIsTerm _
  | JudgementIsTerm _, JudgementIsType _ ->
     Error.raise InvalidCongruence

let form_is_type sgn ty1 ty2 =
  match ty1, ty2 with

  | TypeConstructor (c, args1), TypeConstructor (c', args2) ->
     if not (Ident.equal c c') then
       None
     else
       let form eq_args concl =
         match concl with
         | BoundaryIsType () ->
            let asmp = Collect_assumptions.arguments eq_args in
            Mk.eq_type asmp ty1 ty2

         | BoundaryIsTerm _ | BoundaryEqType _ | BoundaryEqTerm _ ->
            assert false
       in
       let rl = Signature.lookup_rule c sgn in
       Some (form_rule_rap sgn form rl args1 args2)

  | TypeMeta (MetaFree {meta_nonce=n1; meta_boundary}, args1), TypeMeta (MetaFree {meta_nonce=n2;_}, args2) ->
     let abstr = (match Boundary.as_is_type_abstraction meta_boundary with Some abstr -> abstr | None -> assert false) in
     if not (Nonce.equal n1 n2) then
       None
     else
       Some (form_meta_rap
               (fun eq_args () ->
                 let asmp = Collect_assumptions.arguments eq_args in
                 Mk.eq_type asmp ty1 ty2)
               abstr
               args1 args2)

  | TypeMeta (MetaBound _, _), _ | _, TypeMeta (MetaBound _, _)
  | TypeConstructor _, TypeMeta _
  | TypeMeta _, TypeConstructor _ ->
        None

let form_is_term sgn e1 e2 =
  let rec form = function
    | TermConvert (e1, _, _), e2 -> form (e1, e2)

    | e1, TermConvert (e2, _, _) -> form (e1, e2)

    | TermConstructor (c, args1), TermConstructor (c', args2) ->
       if not (Ident.equal c c') then
         None
       else
         let form' eq_args concl =
           match concl with
           | BoundaryIsTerm t_schema ->
              let asmp = Collect_assumptions.arguments eq_args
              and t = Instantiate_meta.is_type ~lvl:0 (List.rev args1) t_schema in
              Mk.eq_term asmp e1 e2 t

           | BoundaryIsType _ | BoundaryEqType _ | BoundaryEqTerm _ ->
              assert false
         in
         let rl = Signature.lookup_rule c sgn in
         Some (form_rule_rap sgn form' rl args1 args2)

    | (TermMeta (MetaFree {meta_nonce=n1; meta_boundary}, args1) as e1), (TermMeta (MetaFree {meta_nonce=n2;_}, args2) as e2) ->
       let abstr = (match Boundary.as_is_term_abstraction meta_boundary with Some abstr -> abstr | None -> assert false) in
       if not (Nonce.equal n1 n2) then
         None
       else
         Some (form_meta_rap
                 (fun eq_args t' ->
                   let t = Instantiate_bound.is_type_fully (Indices.of_list args1) t' in
                   let asmp = Collect_assumptions.arguments eq_args in
                   Mk.eq_term asmp e1 e2 t)
                 abstr
                 args1 args2)

    | TermAtom x as e1, TermAtom y ->
       if Nonce.equal x.atom_nonce y.atom_nonce then
         let eq = Form.reflexivity_term sgn e1 in
         Some (RapDone eq)
       else
         None

    | TermMeta _, (TermConstructor _ | TermAtom _)
    | TermConstructor _, (TermMeta _ | TermAtom _)
    | TermAtom _, (TermMeta _ | TermConstructor _) ->
       None

    | TermMeta (MetaBound _, _), _ | _, TermMeta (MetaBound _, _)
      | TermBoundVar _, _ | _, TermBoundVar _ -> assert false
  in
  form (e1, e2)
