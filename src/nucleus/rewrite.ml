(** Rewrite a constructor according to equations for arguments and output the equation between the judgements *)

open Nucleus_types

exception Skip_argument

let convert_argument sgn es asmps prem arg jdg =
  let rec fold prem arg jdg =
    match prem, arg, jdg with
      | NotAbstract bdry, Arg_NotAbstract arg, NotAbstract jdg ->
        begin match bdry, arg, jdg with
        | BoundaryIsType (), JudgementIsType t1, JudgementEqType (EqType (asmp, t1', t2)) ->
          if Alpha_equal.is_type t1 t1' then
          asmp, NotAbstract (JudgementIsType t2)
          else Error.raise InvalidRewrite

        | BoundaryIsTerm t_schema, JudgementIsTerm e1, JudgementEqTerm (EqTerm (asmp, e1', e2, t)) ->
          if Alpha_equal.is_term e1 e1' then
          let es_arg = List.map Coerce.to_argument es in
          let t' = Instantiate_meta.is_type ~lvl:0 es_arg t_schema in
          let asmp' = asmps in
          asmp,  NotAbstract (JudgementIsTerm (TermConvert (e2, asmp', t')))
          else Error.raise InvalidRewrite

        | BoundaryEqType _, JudgementEqType _, JudgementEqType _
        | BoundaryEqTerm _, JudgementEqTerm _, JudgementEqTerm _ ->
          raise Skip_argument

        | _ -> Error.raise InvalidRewrite
      end


      | Abstract (x, t_schema, prem'), Arg_Abstract (x1, arg1), Abstract (x2, t, jdg') ->
        let x = Name.prefer (Name.prefer x1 x2) x in
        let es_arg = List.map Coerce.to_argument es in
        let t' = Instantiate_meta.is_type ~lvl:0 es_arg t_schema in
        let atm = Mk.fresh_atom x t in
        let atm_jdg  = Mk.atom(atm) in
        let prem' = Instantiate_bound.(abstraction boundary atm_jdg prem')
        and arg1 = Instantiate_bound.(argument ~lvl:0 atm_jdg arg1)
        and jdg' = Instantiate_bound.(abstraction judgement atm_jdg jdg') in
        let asmp', abstr' = fold prem' arg1 jdg' in
        let a = Mk.fresh_atom x t' in
        (* Here the converts are not piled, because we convert an atom *)
        let a_conv = Mk.term_convert_panic (Mk.atom a) asmps t in
        let abstr = Abstract.judgement_abstraction atm abstr' in
        let abstr = Apply_abstraction.apply_judgement_abstraction sgn abstr a_conv in
        let asmp' = Abstract.assumptions atm.atom_nonce asmp' in
        (* let asmp' = Apply_abstraction.apply_assumptions  *)
        (* let abstr = Instantiate_bound.(abstraction judgement ~lvl:0 a_conv abstr') in *)
        asmp', Abstract.judgement_abstraction a abstr


      | Abstract _, Arg_NotAbstract _, NotAbstract _
      | NotAbstract _, Arg_Abstract _, NotAbstract _
      | Abstract _, Arg_Abstract _, NotAbstract _
      | NotAbstract _, Arg_NotAbstract _, Abstract _
      | Abstract _, Arg_NotAbstract _, Abstract _
      | NotAbstract _, Arg_Abstract _, Abstract _ ->
         Error.raise InvalidRewrite

  in
  try
    fold prem arg jdg
  with
  | Skip_argument -> Error.raise InvalidRewrite


let is_type sgn t jdg_lst =
  match t with
  | TypeConstructor(c, args) ->
      let rl = Signature.lookup_rule c sgn in
      let rec fold es asmps rl args jdg_lst =
        begin match rl, args, jdg_lst with
        | Conclusion BoundaryIsType (), [], [] ->
          let es = List.rev (List.map Coerce.to_argument es) in
          let t' = Mk.type_constructor c es in
          (Mk.eq_type asmps t t'), t'


        | Premise ({meta_boundary=prem;_}, rl), arg :: args, jdg :: jdg_lst ->
          let asmp, jdg' = convert_argument sgn es asmps prem arg jdg in
          let asmps = Assumption.union asmps asmp in
          fold (jdg' :: es) asmps rl args jdg_lst

        | Conclusion BoundaryIsTerm _, [], []
        | Conclusion BoundaryEqType _, [], []
        | Conclusion BoundaryEqTerm _, [], []
        | Conclusion _, _::_, _
        | Conclusion _, [], _::_
        | Premise _, [], _
        | Premise _, _::_, [] ->
           Error.raise InvalidRewrite
          end
        in
        fold [] Assumption.empty rl args jdg_lst

  | TypeMeta ((MetaFree {meta_nonce=n; meta_boundary} as m), args) ->
      let rec fold es asmps bdry args jdg_lst =
        begin
        match bdry, args, jdg_lst with
        | NotAbstract (BoundaryIsType ()), [], [] ->
          let asmp = asmps in
          let t' = Mk.type_meta m (List.rev es) in
          (Mk.eq_type asmp t t'),  t'

        | Abstract (_, t', abstr), arg :: args, jdg :: jdg_lst  ->
          let es_jdg = List.map (fun e -> Coerce.from_is_term_abstraction (Abstract.not_abstract e)) es in
          let prem = Abstract.not_abstract (Form.form_is_term_boundary t') in
          let asmp, jdg' = convert_argument sgn es_jdg asmps prem arg jdg in
          let asmps = Assumption.union asmps asmp in
          let e =
            begin
            match jdg' with
            | Abstract _ -> Error.raise InvalidRewrite
            | NotAbstract e ->
              begin
                match Coerce.as_is_term (e) with
                | Some x -> x
                | None -> Error.raise InvalidRewrite
              end
          end  in
          fold (e :: es) asmps abstr args jdg_lst


            | NotAbstract (BoundaryIsTerm _| BoundaryEqType _|BoundaryEqTerm _), _, _
            | NotAbstract _, _::_, _
            | NotAbstract _, _, _::_
            | Abstract _, [], _
            | Abstract _, _, [] ->
               Error.raise InvalidCongruence
          end
      in
      let args = List.map (fun x -> Coerce.to_argument (Abstract.not_abstract (JudgementIsTerm x))) args in
      fold [] Assumption.empty meta_boundary args jdg_lst

  | TypeMeta (MetaBound _, _) -> Error.raise InvalidRewrite


let rec is_term sgn e jdg_lst =
  match e with
  | TermConstructor(c, args) ->
    let rl = Signature.lookup_rule c sgn in
    let rec fold es asmps rl args jdg_lst =
      begin match rl, args, jdg_lst with
      | Conclusion BoundaryIsTerm t, [], [] ->
        let es = List.map Coerce.to_argument es in
        let t = Instantiate_meta.is_type ~lvl:0 es t in
        let es = List.rev es in
        let e' = Mk.term_constructor c es in
        let t' = Sanity.type_of_term sgn e' in
        (* Assumptions on previous equalities witness the equality of types. *)
        let t'_eq_t = Mk.eq_type asmps t' t in
        let e'= Form_convert.is_term_convert sgn e' t'_eq_t in
        (Mk.eq_term asmps e e' t), e'


      | Premise ({meta_boundary=prem;_}, rl), arg :: args, jdg :: jdg_lst ->
        let asmp, jdg' = convert_argument sgn es asmps prem arg jdg in
        let asmps = Assumption.union asmps asmp in
        fold (jdg' :: es) asmps rl args jdg_lst

      | Conclusion BoundaryIsType _, [], []
      | Conclusion BoundaryEqType _, [], []
      | Conclusion BoundaryEqTerm _, [], []
      | Conclusion _, _::_, _
      | Conclusion _, [], _::_
      | Premise _, [], _
      | Premise _, _::_, [] ->
        Error.raise InvalidRewrite
      end
    in
    fold [] Assumption.empty rl args jdg_lst

  | TermMeta ((MetaFree {meta_nonce=n; meta_boundary} as m), args) ->
    let rec fold es asmps bdry args jdg_lst =
      begin
      match bdry, args, jdg_lst with
      | NotAbstract (BoundaryIsTerm t), [], [] ->
        let asmp = asmps in
        let e' = Mk.term_meta m (List.rev es) in
        let e' = Form_convert.is_term_convert sgn e' (Mk.eq_type asmps (Sanity.type_of_term sgn e') t) in
        (Mk.eq_term asmp e e' t), e'

      | Abstract (_, t', abstr), arg :: args, jdg :: jdg_lst  ->
        let es_jdg = List.map (fun e -> Coerce.from_is_term_abstraction (Abstract.not_abstract e)) es in
        let prem = Abstract.not_abstract (Form.form_is_term_boundary t') in
        let asmp, jdg' = convert_argument sgn es_jdg asmps prem arg jdg in
        let asmps = Assumption.union asmps asmp in
        let e =
          begin
          match jdg' with
          | Abstract _ -> Error.raise InvalidRewrite
          | NotAbstract e ->
            begin
              match Coerce.as_is_term (e) with
              | Some x -> x
              | None -> Error.raise InvalidRewrite
              end
            end  in
        fold (e :: es) asmps abstr args jdg_lst


      | NotAbstract (BoundaryIsType _| BoundaryEqType _|BoundaryEqTerm _), _, _
      | NotAbstract _, _::_, _
      | NotAbstract _, _, _::_
      | Abstract _, [], _
      | Abstract _, _, [] ->
         Error.raise InvalidCongruence
      end
      in
      let args = List.map (fun x -> Coerce.to_argument (Abstract.not_abstract (JudgementIsTerm x))) args in
      fold [] Assumption.empty meta_boundary args jdg_lst

  | TermConvert (e', asmp, t) ->
    begin
    match is_term sgn e' jdg_lst with
    | (EqTerm (asmps, e1, e2, t') as eq), e'' ->
      let t''_eq_t = Mk.eq_type asmp (Sanity.type_of_term sgn e'') t in
      (Form_convert.eq_term_convert eq (Mk.eq_type asmp t' t)), (Form_convert.is_term_convert sgn e'' t''_eq_t)
    end

  | TermBoundVar _
  | TermAtom _ ->
    begin
    match jdg_lst with
    | [] -> (Form.reflexivity_term sgn e), e
    | _ :: _ -> Error.raise InvalidRewrite
    end
  | TermMeta (MetaBound _, _) -> Error.raise InvalidRewrite


let judgement sgn jdg jdg_lst =
  match jdg with

  | JudgementIsType t ->
    let t_eq_t', t' = is_type sgn t jdg_lst in
    JudgementEqType t_eq_t', JudgementIsType t'

  | JudgementIsTerm e ->
    let e_eq_e', e' = is_term sgn e jdg_lst in
    JudgementEqTerm e_eq_e', JudgementIsTerm e'

  | JudgementEqType _ | JudgementEqTerm _ -> Error.raise InvalidRewrite
