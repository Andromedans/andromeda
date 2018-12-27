let (>>=) = Runtime.bind
let return = Runtime.return

(** Matching *)

exception Match_fail

let add_var x (v : Runtime.value) xvs = v :: xvs

(* There is a lot of repetition in the [collect_is_XYZ] functions below,
   but this seems to be the price to pay for the discrepancy between the
   syntax of patterns and the structure of runtime values. *)

(* Collect the values of the matched bound variables and return them in a list. The head
   of the list is the *last* variable found, which means that probably the list should be
   reversed before we actually put the values onto the environment. *)
let rec collect_is_term env xvs {Location.thing=p';loc} v =
  match p' with
  (* patterns that are generic for all judgement forms *)
  | Pattern.TTAnonymous -> xvs

  | Pattern.TTVar x ->
     add_var x (Runtime.mk_is_term v) xvs

  | Pattern.TTAs (p1, p2) ->
     let xvs = collect_is_term env xvs p1 v in
     collect_is_term env xvs p2 v

  (* patterns specific to terms *)
  | Pattern.TTConstructor (c, ps) ->
     begin match Nucleus.as_not_abstract v with
     | None -> Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_is_term v)))
     | Some e ->
        let sgn = Runtime.get_signature env in
        begin match Nucleus.invert_is_term sgn e with
        | Nucleus.Stump_TermConstructor (c', args) when Name.eq_ident c c' ->
           begin
             match collect_args env xvs ps args with
             | None -> Runtime.(error ~loc (InvalidPatternMatch (mk_is_term v)))
             | Some vs -> vs
           end
        | Nucleus.(Stump_TermConstructor _ | Stump_TermMeta _ | Stump_TermAtom _ | Stump_TermConvert _) ->
           raise Match_fail
        end
     end

  | Pattern.TTGenAtom p ->
     begin match Nucleus.as_not_abstract v with
     | None -> Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_is_term v)))
     | Some e ->
        let sgn = Runtime.get_signature env in
        begin match Nucleus.invert_is_term sgn e with
        | Nucleus.Stump_TermAtom a ->
           collect_is_term env xvs p v
        | Nucleus.(Stump_TermConstructor _ | Stump_TermMeta _ | Stump_TermConvert _) ->
           raise Match_fail
        end
     end

  | Pattern.TTIsTerm (p1, p2) ->
     let xvs = collect_is_term env xvs p1 v in
     (* TODO optimize for the case when [p2] is [Pattern.TTAnonymous]
        because it allows us to avoid calculating the type of [v]. *)
     let sgn = Runtime.get_signature env in
     let t = Nucleus.type_of_term_abstraction sgn v in
     collect_is_type env xvs p2 t

  | Pattern.TTAbstract (xopt, p1, p2) ->
     begin match Nucleus.invert_is_term_abstraction v with
     | Nucleus.Stump_NotAbstract _ -> Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_is_term v)))
     | Nucleus.Stump_Abstract (a, v2) ->
        let v1 = Nucleus.abstract_not_abstract (Nucleus.type_of_atom a) in
        let xvs = collect_is_type env xvs p1 v1 in
        let xvs =
          match xopt with
          | None -> xvs
          | Some x ->
             let e = Nucleus.abstract_not_abstract (Nucleus.form_is_term_atom a) in
             add_var x (Runtime.mk_is_term e) xvs
        in
        collect_is_term env xvs p2 v
     end

  | (Pattern.TTEqType _ | Pattern.TTEqTerm _ | Pattern.TTIsType _) ->
     Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_is_term v)))

and collect_is_type env xvs {Location.thing=p';loc} v =
  match p' with
  (* patterns that are generic for all judgement forms *)
  | Pattern.TTAnonymous -> xvs

  | Pattern.TTVar x ->
     add_var x (Runtime.mk_is_type v) xvs

  | Pattern.TTAs (p1, p2) ->
     let xvs = collect_is_type env xvs p1 v in
     collect_is_type env xvs p2 v

  (* patterns specific to types *)
  | Pattern.TTConstructor (c, ps) ->
     begin match Nucleus.as_not_abstract v with
     | None -> Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_is_type v)))
     | Some t ->
        begin match Nucleus.invert_is_type t with
        | Nucleus.Stump_TypeConstructor (c', args) when Name.eq_ident c c' ->
           begin
             match collect_args env xvs ps args with
             | None -> Runtime.(error ~loc (InvalidPatternMatch (mk_is_type v)))
             | Some vs -> vs
           end
        | Nucleus.(Stump_TypeConstructor _ | Stump_TypeMeta _) -> raise Match_fail
        end
     end

  | Pattern.TTAbstract (xopt, p1, p2) ->
     begin match Nucleus.invert_is_type_abstraction v with
     | Nucleus.Stump_NotAbstract _ -> Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_is_type v)))
     | Nucleus.Stump_Abstract (a, v2) ->
        let v1 = Nucleus.abstract_not_abstract (Nucleus.type_of_atom a) in
        let xvs = collect_is_type env xvs p1 v1 in
        let xvs =
          match xopt with
          | None -> xvs
          | Some x ->
             let e = Nucleus.abstract_not_abstract (Nucleus.form_is_term_atom a) in
             add_var x (Runtime.mk_is_term e) xvs
        in
        collect_is_type env xvs p2 v
     end

  | (Pattern.TTIsTerm _ | Pattern.TTGenAtom _ | Pattern.TTEqType _ |
     Pattern.TTEqTerm _ | Pattern.TTIsType _) ->
     Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_is_type v)))

and collect_eq_type env xvs {Location.thing=p';loc} v =
  match p' with
  (* patterns that are generic for all judgement forms *)
  | Pattern.TTAnonymous -> xvs

  | Pattern.TTVar x ->
     add_var x (Runtime.mk_eq_type v) xvs

  | Pattern.TTAs (p1, p2) ->
     let xvs = collect_eq_type env xvs p1 v in
     collect_eq_type env xvs p2 v

  (* patterns specific to type equations *)
  | Pattern.TTAbstract (xopt, p1, p2) ->
     begin match Nucleus.invert_eq_type_abstraction v with
     | Nucleus.Stump_NotAbstract _ -> Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_eq_type v)))
     | Nucleus.Stump_Abstract (a, v2) ->
        let v1 = Nucleus.abstract_not_abstract (Nucleus.type_of_atom a) in
        let xvs = collect_is_type env xvs p1 v1 in
        let xvs =
          match xopt with
          | None -> xvs
          | Some x ->
             let e = Nucleus.abstract_not_abstract (Nucleus.form_is_term_atom a) in
             add_var x (Runtime.mk_is_term e) xvs
        in
        collect_eq_type env xvs p2 v
     end

  | Pattern.TTEqType (p1, p2) ->
     begin match Nucleus.as_not_abstract v with
     | None -> Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_eq_type v)))
     | Some eq ->
        let (Nucleus.Stump_EqType (_asmp, t1, t2)) = Nucleus.invert_eq_type eq in
        let xvs = collect_is_type env xvs p1 (Nucleus.abstract_not_abstract t1) in
        collect_is_type env xvs p2 (Nucleus.abstract_not_abstract t2)
     end

  | (Pattern.TTIsTerm _ | Pattern.TTGenAtom _ | Pattern.TTEqTerm _ | Pattern.TTIsType _ |
     Pattern.TTConstructor _) ->
     Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_eq_type v)))

and collect_eq_term env xvs {Location.thing=p';loc} v =
  match p' with
  (* patterns that are generic for all judgement forms *)
  | Pattern.TTAnonymous -> xvs

  | Pattern.TTVar x ->
     add_var x (Runtime.mk_eq_term v) xvs

  | Pattern.TTAs (p1, p2) ->
     let xvs = collect_eq_term env xvs p1 v in
     collect_eq_term env xvs p2 v

  (* patterns specific to term equations *)
  | Pattern.TTAbstract (xopt, p1, p2) ->
     begin match Nucleus.invert_eq_term_abstraction v with
     | Nucleus.Stump_NotAbstract _ -> Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_eq_term v)))
     | Nucleus.Stump_Abstract (a, v2) ->
        let v1 = Nucleus.abstract_not_abstract (Nucleus.type_of_atom a) in
        let xvs = collect_is_type env xvs p1 v1 in
        let xvs =
          match xopt with
          | None -> xvs
          | Some x ->
             let e = Nucleus.abstract_not_abstract (Nucleus.form_is_term_atom a) in
             add_var x (Runtime.mk_is_term e) xvs
        in
        collect_eq_term env xvs p2 v
     end

  | Pattern.TTEqTerm (p1, p2, p3) ->
     begin match Nucleus.as_not_abstract v with
     | None -> Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_eq_term v)))
     | Some eq ->
        let (Nucleus.Stump_EqTerm (_asmp, e1, e2, t)) = Nucleus.invert_eq_term eq in
        let xvs = collect_is_term env xvs p1 (Nucleus.abstract_not_abstract e1) in
        let xvs = collect_is_term env xvs p2 (Nucleus.abstract_not_abstract e2) in
        collect_is_type env xvs p2 (Nucleus.abstract_not_abstract t)
     end

  | (Pattern.TTIsTerm _ | Pattern.TTGenAtom _ | Pattern.TTEqType _ | Pattern.TTIsType _ |
     Pattern.TTConstructor _) ->
     Runtime.(error ~loc (InvalidPatternMatch (Runtime.mk_eq_term v)))

and collect_args env xvs ps vs =
  match ps, vs with

  | [], [] -> Some xvs

  | p::ps, v::vs ->
     let xvs =
       begin match v with
       | Nucleus.ArgumentIsType t -> collect_is_type env xvs p t
       | Nucleus.ArgumentIsTerm e -> collect_is_term env xvs p e
       | Nucleus.ArgumentEqType eq -> collect_eq_type env xvs p eq
       | Nucleus.ArgumentEqTerm eq -> collect_eq_term env xvs p eq
     end in
     collect_args env xvs ps vs

  | [], _::_ | _::_, [] -> None

and collect_pattern env xvs {Location.thing=p';loc} v =
  match p', v with
  | Pattern.Anonymous, _ -> xvs

  | Pattern.Var x, v ->
     add_var x v xvs

  | Pattern.As (p1, p2), v ->
     let xvs = collect_pattern env xvs p1 v in
     collect_pattern env xvs p2 v

  | Pattern.Judgement p, Runtime.IsType t ->
     collect_is_type env xvs p t

  | Pattern.Judgement p, Runtime.IsTerm e ->
     collect_is_term env xvs p e

  | Pattern.Judgement p, Runtime.EqType eq ->
     collect_eq_type env xvs p eq

  | Pattern.Judgement p, Runtime.EqTerm eq ->
     collect_eq_term env xvs p eq

  | Pattern.AMLConstructor (tag, ps), Runtime.Tag (tag', vs) ->
     if not (Name.eq_ident tag tag')
     then
       raise Match_fail
     else
       begin
         match multicollect_pattern env xvs ps vs with
         | None -> Runtime.(error ~loc (InvalidPatternMatch v))
         | Some vs -> vs
       end

  | Pattern.Tuple ps, Runtime.Tuple vs ->
    begin
      match multicollect_pattern env xvs ps vs with
      | None -> Runtime.(error ~loc (InvalidPatternMatch v))
      | Some vs -> vs
    end

  (* mismatches *)
  | Pattern.Judgement _, (Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ |
                          Runtime.Ref _ | Runtime.Dyn _ |
                          Runtime.Tuple _ | Runtime.String _)

  | Pattern.AMLConstructor _, (Runtime.IsTerm _ | Runtime.IsType _ | Runtime.EqTerm _ | Runtime.EqType _ |
                               Runtime.Closure _ | Runtime.Handler _ |
                               Runtime.Ref _ | Runtime.Dyn _ |
                               Runtime.Tuple _ | Runtime.String _)

  | Pattern.Tuple _, (Runtime.IsTerm _ | Runtime.IsType _ | Runtime.EqTerm _ | Runtime.EqType _ |
                      Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ |
                      Runtime.Ref _ | Runtime.Dyn _ | Runtime.String _) ->
     Runtime.(error ~loc (InvalidPatternMatch v))

and multicollect_pattern env xvs ps vs =
  let rec fold xvs = function
    | [], [] -> Some xvs
    | p::ps, v::vs ->
      let xvs = collect_pattern env xvs p v in
      fold xvs (ps, vs)
    | ([], _::_ | _::_, []) ->
       None
  in
  fold xvs (ps, vs)

let match_pattern_env p v env =
  try
    let xvs = collect_pattern env [] p v in
    Some xvs
  with
    Match_fail -> None

let top_match_pattern p v =
  let (>>=) = Runtime.top_bind in
  Runtime.top_get_env >>= fun env ->
    let r = match_pattern_env p v env  in
    Runtime.top_return r

let match_pattern p v =
  (* collect values of pattern variables *)
  Runtime.get_env >>= fun env ->
  let r = match_pattern_env p v env in
  return r

let match_op_pattern ~loc ps p_out vs t_out =
  Runtime.get_env >>= fun env ->
  let r =
    begin
      try
        let xvs =
          begin
            match multicollect_pattern env [] ps vs with
            | None -> Runtime.(error ~loc InvalidHandlerMatch)
            | Some xvs -> xvs
          end
        in
        let xvs =
          match p_out with
          | None -> xvs
          | Some p ->
             begin match t_out with
             | Some t -> collect_is_type env xvs p t
             | None -> xvs
             end
        in
        Some xvs
      with Match_fail -> None
    end in
  return r
