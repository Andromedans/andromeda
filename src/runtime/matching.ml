let (>>=) = Runtime.bind
let return = Runtime.return

(** Matching *)

exception Match_fail

let add_var (v : Runtime.value) vs = v :: vs

let as_is_term jdg =
  match Nucleus.as_not_abstract jdg with
  | None -> raise Match_fail
  | Some (Nucleus.JudgementIsTerm e) -> e
  | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) -> raise Match_fail

let rec collect_judgement sgn xvs {Location.thing=p';loc} jdg =
  match p' with

  | Rsyntax.Pattern.TTAnonymous -> xvs

  | Rsyntax.Pattern.TTVar ->
     add_var (Runtime.Judgement jdg) xvs

  | Rsyntax.Pattern.TTAs (p1, p2) ->
     let xvs = collect_judgement sgn xvs p1 jdg in
     collect_judgement sgn xvs p2 jdg

  | Rsyntax.Pattern.TTAbstract (xopt, p1, p2) ->
     begin match Nucleus.as_abstract jdg with
     | None -> raise Match_fail
     | Some (a, v2) ->
        let v1 = Nucleus.(abstract_not_abstract (JudgementIsType (type_of_atom a))) in
        let xvs = collect_judgement sgn xvs p1 v1 in
        let xvs =
          match xopt with
          | None -> xvs
          | Some _ ->
             let e = Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom a))) in
             add_var (Runtime.mk_judgement e) xvs
        in
        collect_judgement sgn xvs p2 v2
     end

  | Rsyntax.Pattern.TTConstructor (c, ps) ->
     begin match Nucleus.as_not_abstract jdg with
     | None -> raise Match_fail
     | Some jdg -> collect_constructor sgn xvs c ps jdg
     end

  | Rsyntax.Pattern.TTGenAtom p ->
     let e = as_is_term jdg in
     begin match Nucleus.invert_is_term sgn e with
     | Nucleus.Stump_TermAtom a ->
        collect_judgement sgn xvs p jdg
     | Nucleus.(Stump_TermConstructor _ | Stump_TermMeta _ | Stump_TermConvert _) ->
        raise Match_fail
     end


  | Rsyntax.Pattern.TTIsType p ->
     begin match Nucleus.as_not_abstract jdg with
     | None -> raise Match_fail
     | Some (Nucleus.JudgementIsType _) -> collect_judgement sgn xvs p jdg
     | Some Nucleus.(JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _) -> raise Match_fail
     end

  | Rsyntax.Pattern.TTIsTerm (p1, p2) ->
     (* By computing [e] first, we make sure that we're actually matching against
        a term judgement. If you change the order of evaluation, then it could
        happen that [p1] will match against [jdg] even though [jdg] is not a term
        judgement. *)
     let e = as_is_term jdg in
     let xvs = collect_judgement sgn xvs p1 jdg in
     begin match p2 with
     | {Location.thing=Rsyntax.Pattern.TTAnonymous;_} -> xvs
     | _ ->
        let t = Nucleus.type_of_term sgn e in
        collect_judgement sgn xvs p2 (Nucleus.(abstract_not_abstract (JudgementIsType t)))
     end

  | Rsyntax.Pattern.TTEqType (pt1, pt2) ->
     begin match Nucleus.as_not_abstract jdg with
     | None -> raise Match_fail
     | Some Nucleus.(JudgementIsTerm _ | JudgementIsType _ | JudgementEqTerm _) -> raise Match_fail
     | Some (Nucleus.JudgementEqType eq) ->
        begin match Nucleus.invert_eq_type eq with
        | Nucleus.Stump_EqType (_asmp, t1, t2) ->
           let jdg1 = Nucleus.(abstract_not_abstract (JudgementIsType t1))
           and jdg2 = Nucleus.(abstract_not_abstract (JudgementIsType t2)) in
           let xvs = collect_judgement sgn xvs pt1 jdg1 in
           collect_judgement sgn xvs pt2 jdg2
        end
     end

  | Rsyntax.Pattern.TTEqTerm (pe1, pe2, pt) ->
     begin match Nucleus.as_not_abstract jdg with
     | None -> raise Match_fail
     | Some Nucleus.(JudgementIsTerm _ | JudgementIsType _ | JudgementEqType _) -> raise Match_fail
     | Some (Nucleus.JudgementEqTerm eq) ->
        begin match Nucleus.invert_eq_term eq with
        | Nucleus.Stump_EqTerm (_asmp, e1, e2, t) ->
           let jdg_e1 = Nucleus.(abstract_not_abstract (JudgementIsTerm e1))
           and jdg_e2 = Nucleus.(abstract_not_abstract (JudgementIsTerm e2))
           and jdg_t = Nucleus.(abstract_not_abstract (JudgementIsType t)) in
           let xvs = collect_judgement sgn xvs pe1 jdg_e1 in
           let xvs = collect_judgement sgn xvs pe2 jdg_e2 in
           collect_judgement sgn xvs pt jdg_t
        end
     end

and collect_constructor sgn xvs c ps = function
  | Nucleus.JudgementIsType t ->
     begin match Nucleus.invert_is_type t with
     | Nucleus.Stump_TypeConstructor (c', args) ->
        if Ident.equal c c' then
          collect_arguments sgn xvs ps args
        else
          raise Match_fail
     | Nucleus.Stump_TypeMeta _ -> raise Match_fail
     end

  | Nucleus.JudgementIsTerm e ->
     let rec collect e =
       begin match Nucleus.invert_is_term sgn e with
       | Nucleus.Stump_TermConvert (e, _) ->
          collect e

       | Nucleus.Stump_TermConstructor (c', args) ->
          if Ident.equal c c' then
            collect_arguments sgn xvs ps args
          else
            raise Match_fail

       | Nucleus.(Stump_TermAtom _ | Stump_TermMeta _) ->
          raise Match_fail
       end
     in
     collect e

  | Nucleus.(JudgementEqType eq)  -> raise Match_fail

  | Nucleus.JudgementEqTerm _ -> raise Match_fail

and collect_arguments sgn xvs ps vs =
  match ps, vs with

  | [], [] -> xvs

  | p::ps, v::vs ->
     let xvs = collect_judgement sgn xvs p v in
     collect_arguments sgn xvs ps vs

  | [], _::_ | _::_, [] ->
     (* This should never happen because desugaring checks arities of constructors and patterns. *)
     assert false

let rec collect_pattern sgn xvs {Location.thing=p';loc} v =
  match p', v with
  | Rsyntax.Pattern.Anonymous, _ -> xvs

  | Rsyntax.Pattern.Var, v ->
     add_var v xvs

  | Rsyntax.Pattern.As (p1, p2), v ->
     let xvs = collect_pattern sgn xvs p1 v in
     collect_pattern sgn xvs p2 v

  | Rsyntax.Pattern.Judgement p, Runtime.Judgement jdg ->
     collect_judgement sgn xvs p jdg

  | Rsyntax.Pattern.MLConstructor (tag, ps), Runtime.Tag (tag', vs) ->
     if not (Runtime.equal_tag tag tag')
     then
       raise Match_fail
     else
       begin
         match collect_pattern_list sgn xvs ps vs with
         | None -> Runtime.(error ~loc (InvalidPatternMatch v))
         | Some vs -> vs
       end

  | Rsyntax.Pattern.Tuple ps, Runtime.Tuple vs ->
    begin
      match collect_pattern_list sgn xvs ps vs with
      | None -> Runtime.(error ~loc (InvalidPatternMatch v))
      | Some vs -> vs
    end

  (* mismatches *)
  | Rsyntax.Pattern.Judgement _,
    Runtime.(Boundary _ | Closure _ | Handler _ | Tag _ | Ref _ | Dyn _ | Tuple _ | String _)

  | Rsyntax.Pattern.MLConstructor _,
    Runtime.(Judgement _ | Boundary _ | Closure _ | Handler _ | Ref _ | Dyn _ | Tuple _ | String _)

  | Rsyntax.Pattern.Tuple _,
    Runtime.(Judgement _ | Boundary _ | Closure _ | Handler _ | Tag _ | Ref _ | Dyn _ | String _) ->
     Runtime.(error ~loc (InvalidPatternMatch v))

and collect_pattern_list sgn xvs ps vs =
  let rec fold xvs = function
    | [], [] -> Some xvs
    | p::ps, v::vs ->
      let xvs = collect_pattern sgn xvs p v in
      fold xvs (ps, vs)
    | ([], _::_ | _::_, []) ->
       None
  in
  fold xvs (ps, vs)

let match_pattern' sgn p v =
  try
    let xvs = collect_pattern sgn [] p v in
    Some xvs
  with
    Match_fail -> None

let top_match_pattern p v =
  let (>>=) = Runtime.top_bind in
  Runtime.top_get_env >>= fun env ->
  let sgn = Runtime.get_signature env in
  let r = match_pattern' sgn p v in
  Runtime.top_return r

let match_pattern p v =
  (* collect values of pattern variables *)
  Runtime.get_env >>= fun env ->
  let sgn = Runtime.get_signature env in
  let r = match_pattern' sgn p v in
  return r

let collect_boundary_pattern sgn xvs pttrn bdry =
  failwith "pattern matching of boundaries not implemented"

let match_op_pattern ~loc ps p_bdry vs bdry =
  Runtime.get_env >>= fun env ->
  let sgn = Runtime.get_signature env in
  let r =
    begin
      try
        let xvs =
          begin
            match collect_pattern_list sgn [] ps vs with
            | None -> Runtime.(error ~loc InvalidHandlerMatch)
            | Some xvs -> xvs
          end
        in
        let xvs =
          match p_bdry with
          | None -> xvs
          | Some p ->
             begin match bdry with
             | Some t -> collect_boundary_pattern sgn xvs p t
             | None -> xvs
             end
        in
        Some xvs
      with Match_fail -> None
    end in
  return r
