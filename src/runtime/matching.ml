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

let rec collect_pattern sgn xvs {Location.it=p'; at} v =
  match p', v with
  | Syntax.Patt_Anonymous, _ -> xvs

  | Syntax.Patt_Var, v ->
     add_var v xvs

  | Syntax.Patt_As (p1, p2), v ->
     let xvs = collect_pattern sgn xvs p1 v in
     collect_pattern sgn xvs p2 v

  | Syntax.Patt_MLConstructor (tag, ps), Runtime.Tag (tag', vs) ->
     if not (Runtime.equal_tag tag tag')
     then
       raise Match_fail
     else
       collect_patterns sgn xvs ps vs

  | Syntax.Patt_TTConstructor (c, ps), Runtime.Judgement abstr ->
     begin match Nucleus.as_not_abstract abstr with
     | None -> raise Match_fail
     | Some jdg -> collect_constructor sgn xvs c ps jdg
     end

  | Syntax.Patt_GenAtom p, (Runtime.Judgement abstr as v) ->
     let e = as_is_term abstr in
     begin match Nucleus.invert_is_term sgn e with
     | Nucleus.Stump_TermAtom a ->
        collect_pattern sgn xvs p v
     | Nucleus.(Stump_TermConstructor _ | Stump_TermMeta _ | Stump_TermConvert _) ->
        raise Match_fail
     end

  | Syntax.Patt_IsType p, (Runtime.Judgement abstr as v) ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementIsType _) -> collect_pattern sgn xvs p v
     | None | Some Nucleus.(JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _) -> raise Match_fail
     end

  | Syntax.Patt_IsTerm (p1, p2), (Runtime.Judgement abstr as v) ->
     (* By computing [e] first, we make sure that we're actually matching against
        a term judgement. If you change the order of evaluation, then it could
        happen that [p1] will match against [jdg] even though [jdg] is not a term
        judgement. *)
     let e = as_is_term abstr in
     let xvs = collect_pattern sgn xvs p1 v  in
     begin match p2 with
     | {Location.it=Syntax.Patt_Anonymous;_} -> xvs
     | _ ->
        let t = Nucleus.type_of_term sgn e in
        let t_abstr = Nucleus.(abstract_not_abstract (JudgementIsType t)) in
        collect_judgement sgn xvs p2 t_abstr
     end

  | Syntax.Patt_EqType (pt1, pt2), Runtime.Judgement abstr ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementEqType eq) ->
        begin match Nucleus.invert_eq_type eq with
        | Nucleus.Stump_EqType (_asmp, t1, t2) ->
           let t1_abstr = Nucleus.(abstract_not_abstract (JudgementIsType t1))
           and t2_abstr = Nucleus.(abstract_not_abstract (JudgementIsType t2)) in
           let xvs = collect_judgement sgn xvs pt1 t1_abstr in
           collect_judgement sgn xvs pt2 t2_abstr
        end
     | None | Some Nucleus.(JudgementIsTerm _ | JudgementIsType _ | JudgementEqTerm _) ->
        raise Match_fail
     end

  | Syntax.Patt_EqTerm (pe1, pe2, pt), Runtime.Judgement abstr ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.JudgementEqTerm eq) ->
        begin match Nucleus.invert_eq_term eq with
        | Nucleus.Stump_EqTerm (_asmp, e1, e2, t) ->
           let e1_abstr = Nucleus.(abstract_not_abstract (JudgementIsTerm e1))
           and e2_abstr = Nucleus.(abstract_not_abstract (JudgementIsTerm e2))
           and t_abstr = Nucleus.(abstract_not_abstract (JudgementIsType t)) in
           let xvs = collect_judgement sgn xvs pe1 e1_abstr in
           let xvs = collect_judgement sgn xvs pe2 e2_abstr in
           collect_judgement sgn xvs pt t_abstr
        end
     | None | Some Nucleus.(JudgementIsTerm _ | JudgementIsType _ | JudgementEqType _) ->
        raise Match_fail
     end

  | Syntax.Patt_BoundaryIsType, Runtime.Boundary abstr ->
     begin match Nucleus.as_not_abstract abstr with
     | Some Nucleus.BoundaryIsType () -> xvs
     | None | Some Nucleus.(BoundaryIsTerm _ | BoundaryEqType _ | BoundaryEqTerm _) -> raise Match_fail
     end

  | Syntax.Patt_BoundaryIsTerm p, Runtime.Boundary abstr ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.BoundaryIsTerm t) ->
        let t_abstr = Nucleus.(abstract_not_abstract (JudgementIsType t)) in
        collect_judgement sgn xvs p t_abstr
     | None | Some Nucleus.(BoundaryIsType _ | BoundaryEqType _ | BoundaryEqTerm _) -> raise Match_fail
     end

  | Syntax.Patt_BoundaryEqType (pt1, pt2), Runtime.Boundary abstr ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.BoundaryEqType (t1, t2)) ->
        let t1_abstr = Nucleus.(abstract_not_abstract (JudgementIsType t1))
        and t2_abstr = Nucleus.(abstract_not_abstract (JudgementIsType t2)) in
        let xvs = collect_judgement sgn xvs pt1 t1_abstr in
        collect_judgement sgn xvs pt2 t2_abstr
     | None | Some Nucleus.(BoundaryIsTerm _ | BoundaryIsType _ | BoundaryEqTerm _) ->
        raise Match_fail
     end

  | Syntax.Patt_BoundaryEqTerm (pe1, pe2, pt), Runtime.Boundary abstr ->
     begin match Nucleus.as_not_abstract abstr with
     | Some (Nucleus.BoundaryEqTerm eq) ->
        let (e1, e2, t) = Nucleus.invert_eq_term_boundary eq in
           let e1_abstr = Nucleus.(abstract_not_abstract (JudgementIsTerm e1))
           and e2_abstr = Nucleus.(abstract_not_abstract (JudgementIsTerm e2))
           and t_abstr = Nucleus.(abstract_not_abstract (JudgementIsType t)) in
           let xvs = collect_judgement sgn xvs pe1 e1_abstr in
           let xvs = collect_judgement sgn xvs pe2 e2_abstr in
           collect_judgement sgn xvs pt t_abstr
     | None | Some Nucleus.(BoundaryIsTerm _ | BoundaryIsType _ | BoundaryEqType _) ->
        raise Match_fail
     end

  | Syntax.Patt_Abstract (xopt, p1, p2), Runtime.Judgement abstr ->
     let abstr_stump = Nucleus.invert_judgement_abstraction abstr in
     let xvs, abstr' = collect_abstraction sgn xvs xopt p1 abstr_stump in
     collect_judgement sgn xvs p2 abstr'

  | Syntax.Patt_Abstract (xopt, p1, p2), Runtime.Boundary abstr ->
     let abstr_stump = Nucleus.invert_boundary_abstraction abstr in
     let xvs, abstr' = collect_abstraction sgn xvs xopt p1 abstr_stump in
     collect_pattern sgn xvs p2 (Runtime.mk_boundary abstr')

  | Syntax.Patt_Tuple ps, Runtime.Tuple vs ->
     collect_patterns sgn xvs ps vs

  (* mismatches *)
  | Syntax.Patt_MLConstructor _,
    Runtime.(Judgement _ | Boundary _ | Closure _ | Handler _ | Ref _ | Dyn _ | Tuple _ | String _)

  | Syntax.Patt_Abstract _,
    Runtime.(Closure _ | Handler _ | Tag _ | Ref _ | Dyn _ | Tuple _ | String _)

  | Syntax.(Patt_TTConstructor _ | Patt_GenAtom _ | Patt_IsType _ | Patt_IsTerm _ | Patt_EqType _ | Patt_EqTerm _),
    Runtime.(Boundary _ | Closure _ | Handler _ | Tag _ | Ref _ | Dyn _ | Tuple _ | String _)

  | Syntax.(Patt_BoundaryIsType | Patt_BoundaryIsTerm _ | Patt_BoundaryEqType _ | Patt_BoundaryEqTerm _) ,
    Runtime.(Judgement _ | Closure _ | Handler _ | Tag _ | Ref _ | Dyn _ | Tuple _ | String _)

  | Syntax.Patt_Tuple _,
    Runtime.(Judgement _ | Boundary _ | Closure _ | Handler _ | Tag _ | Ref _ | Dyn _ | String _) ->
     Runtime.(error ~at (InvalidPatternMatch v))

and collect_judgement sgn xvs p abstr =
  collect_pattern sgn xvs p (Runtime.mk_judgement abstr)

and collect_abstraction :
   'a . Nucleus.signature -> Runtime.value list -> Name.t option -> Syntax.pattern ->
        'a Nucleus.stump_abstraction -> Runtime.value list * 'a Nucleus.abstraction
= fun sgn xvs xopt p1 abstr_stump ->
  match abstr_stump with
  | Nucleus.Stump_NotAbstract _ -> raise Match_fail
  | Nucleus.Stump_Abstract (a, abstr') ->
     let t_abstr = Nucleus.(abstract_not_abstract (JudgementIsType (type_of_atom a))) in
     let xvs = collect_judgement sgn xvs p1 t_abstr in
     let xvs =
       match xopt with
       | None -> xvs
       | Some _ ->
          let a_abstr = Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom a))) in
          add_var (Runtime.mk_judgement a_abstr) xvs
     in
     (xvs, abstr')

and collect_constructor sgn xvs c ps = function
  | Nucleus.JudgementIsType t ->
     begin match Nucleus.invert_is_type sgn t with
     | Nucleus.Stump_TypeConstructor (c', args) ->
        if Ident.equal c c' then
          let args = List.map Runtime.mk_judgement args in
          collect_patterns sgn xvs ps args
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
            let args = List.map Runtime.mk_judgement args in
            collect_patterns sgn xvs ps args
          else
            raise Match_fail

       | Nucleus.(Stump_TermAtom _ | Stump_TermMeta _) ->
          raise Match_fail
       end
     in
     collect e

  | Nucleus.(JudgementEqType eq)  -> raise Match_fail

  | Nucleus.JudgementEqTerm _ -> raise Match_fail

and collect_patterns sgn xvs ps vs =
  match ps, vs with

  | [], [] -> xvs

  | p::ps, v::vs ->
     let xvs = collect_pattern sgn xvs p v in
     collect_patterns sgn xvs ps vs

  | [], _::_ | _::_, [] ->
     (* This should never happen because desugaring checks arities of constructors and patterns. *)
     assert false


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

let match_op_pattern ps p_bdry vs bdry =
  Runtime.get_env >>= fun env ->
  let sgn = Runtime.get_signature env in
  let r =
    begin
      try
        let xvs = collect_patterns sgn [] ps vs in
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
