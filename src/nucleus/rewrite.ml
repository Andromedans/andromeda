(** Rewrite a constructor according to equations for arguments and output the equation between the judgements *)

open Nucleus_types

exception Skip_argument

let convert_argument sgn es asmps prem arg jdg =
  let rec fold ~lvl prem arg jdg =
    match prem, arg, jdg with
      | NotAbstract bdry, Arg_NotAbstract arg, NotAbstract jdg ->
        begin match bdry, arg, jdg with
       | BoundaryIsType (), JudgementIsType t1, JudgementEqType (EqType (asmp, t1', t2)) ->
          if Alpha_equal.is_type t1 t1' then
          (let control_bound_meta  = (Collect_assumptions.is_type t2).bound_meta in
          assert (Bound_set.is_empty control_bound_meta);
          assert (Bound_set.is_empty asmp.bound_meta);
          asmp, NotAbstract (JudgementIsType t2))
          else Error.raise InvalidRewrite

       | BoundaryIsTerm t_schema, JudgementIsTerm e1, JudgementEqTerm (EqTerm (asmp, e1', e2, t)) ->
          if Alpha_equal.is_term e1 e1' then
          let es_arg = List.map Coerce.to_argument es in
          let t' = Instantiate_meta.is_type ~lvl es_arg t_schema in
          let control_bound_meta  = (Collect_assumptions.is_type t').bound_meta in
          assert (Bound_set.is_empty control_bound_meta);
          (* Format.printf "assumption bound metas type %b@." (Bound_set.is_empty control_bound_meta); *)
          let asmp' = asmps in
          assert (Bound_set.is_empty asmp.bound_meta);
          assert (Bound_set.is_empty asmp'.bound_meta);
          (* Format.printf "assumption bound metas %b@." (Bound_set.is_empty asmp.bound_meta); *)
          (* Format.printf "assumption bound metas in termconvert %b@." (Bound_set.is_empty asmp'.bound_meta); *)
          asmp,  NotAbstract (JudgementIsTerm (TermConvert (e2, asmp', t')))
          else Error.raise InvalidRewrite

       | BoundaryEqType _, JudgementEqType _, JudgementEqType _
       | BoundaryEqTerm _, JudgementEqTerm _, JudgementEqTerm _ ->
          raise Skip_argument

       | _ -> Error.raise InvalidRewrite
       end


      | Abstract (x, t_schema, prem), Arg_Abstract (x1, arg1), Abstract (x2, t, jdg) ->
        let asmp', abstr' = fold ~lvl:(lvl+1) prem arg1 jdg in
        (* XXX: Make sure the levels of instantiation are correct!! *)
        let x = Name.prefer (Name.prefer x1 x2) x in
        let es_arg = List.map Coerce.to_argument es in
        let t' = Instantiate_meta.is_type ~lvl es_arg t_schema in
        let a = Mk.fresh_atom x t' in
        let a_conv = Mk.term_convert (Mk.atom a) asmps t in
        assert (Bound_set.is_empty asmps.bound_meta);
        assert (Bound_set.is_empty asmp'.bound_meta);
        (* Format.printf "assumption bound metas in term convert %b@." (Bound_set.is_empty asmps.bound_meta); *)
        (* XXX: Are converts going to be piled?? *)
        let abstr = Instantiate_bound.(abstraction judgement ~lvl a_conv abstr') in
        let control_asmp1 = (Collect_assumptions.is_type t').bound_meta in
        let control_asmp2 = (Collect_assumptions.(abstraction judgement abstr)).bound_meta in
        assert (Bound_set.is_empty control_asmp1);
        assert (Bound_set.is_empty control_asmp2);
        assert (Bound_set.is_empty (Collect_assumptions.is_type t).bound_meta);
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
    fold ~lvl:0 prem arg jdg
  with
  | Skip_argument -> Error.raise InvalidRewrite


let is_type sgn t jdg_lst =
  match t with
  | TypeConstructor(c, args) ->
      let rl = Signature.lookup_rule c sgn in
        let rec fold es asmps rl args jdg_lst =
          begin match rl, args, jdg_lst with
            | Conclusion BoundaryIsType (), [], [] ->
              let asmp = Assumption.union asmps (Collect_assumptions.is_type t) in
              assert (Bound_set.is_empty asmp.bound_meta);
              (* Format.printf "assumption bound metas %b@." (Bound_set.is_empty asmp.bound_meta); *)
              let es = List.rev (List.map Coerce.to_argument es) in
              let t' = Mk.type_constructor c es in
              assert (Bound_set.is_empty (Collect_assumptions.is_type t').bound_meta);
              (Mk.eq_type asmp t t'), t'


            | Premise ({meta_boundary=prem;_}, rl), arg :: args, jdg :: jdg_lst ->
              let asmp, jdg' = convert_argument sgn es asmps prem arg jdg in
              let asmps = Assumption.union asmps asmp in
              assert (Bound_set.is_empty (Collect_assumptions.(abstraction judgement jdg')).bound_meta);
              assert (Bound_set.is_empty asmps.bound_meta);
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
            (* let asmp = Assumption.union asmps (Collect_assumptions.is_type t) in *)
            let asmp = asmps in
            assert (Bound_set.is_empty asmp.bound_meta);
            (* Format.printf "assumption bound metas %b@." (Bound_set.is_empty asmp.bound_meta); *)
            (*XXX: Are here asmp just asmps? *)
            let t' = Mk.type_meta m es in
            assert (Bound_set.is_empty (Collect_assumptions.is_type t').bound_meta);
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
              assert (Bound_set.is_empty (Collect_assumptions.(abstraction judgement jdg')).bound_meta);
              assert (Bound_set.is_empty asmps.bound_meta);
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
              let asmp = Assumption.union asmps (Collect_assumptions.is_term e) in
              let es = List.map Coerce.to_argument es in
              let t = Instantiate_meta.is_type ~lvl:0 es t in
              let es = List.rev es in
              let e' = Mk.term_constructor c es in
              let e'= Mk.term_convert e' asmps t in
              assert (Bound_set.is_empty asmp.bound_meta);
              assert (Bound_set.is_empty (Collect_assumptions.is_type t).bound_meta);
              (* Format.printf "assumption bound metas %b@." (Bound_set.is_empty asmp.bound_meta); *)
              (Mk.eq_term asmp e e' t), e'


            | Premise ({meta_boundary=prem;_}, rl), arg :: args, jdg :: jdg_lst ->
              let asmp, jdg' = convert_argument sgn es asmps prem arg jdg in
              let asmps = Assumption.union asmps asmp in
              assert (Bound_set.is_empty asmps.bound_meta);
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
            (* let asmp = Assumption.union asmps (Collect_assumptions.is_type t) in *)
            let asmp = asmps in
            (*XXX: Are here asmp just asmps? *)
            let e' = Mk.term_meta m es in
            let e' = Mk.term_convert e' asmps t in
            assert (Bound_set.is_empty asmp.bound_meta);
            (* Format.printf "assumption bound metas %b@." (Bound_set.is_empty asmp.bound_meta); *)
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
              assert (Bound_set.is_empty asmps.bound_meta);
              assert (Bound_set.is_empty (Collect_assumptions.is_term e).bound_meta);
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
      assert (Bound_set.is_empty (Collect_assumptions.is_type t).bound_meta);
      assert (Bound_set.is_empty (Collect_assumptions.is_type t').bound_meta);
      assert (Bound_set.is_empty asmp.bound_meta);
      (Form.form_eq_term_convert eq (Mk.eq_type asmp t' t)), (Mk.term_convert e'' asmp t)
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

