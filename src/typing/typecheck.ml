(** Bidirectional Hindley-Milner typechecking. *)

let (>>=) = Tyenv.(>>=)
let return = Tyenv.return

let locate ~loc v = Location.locate v loc

let return_located ~loc v = return (locate ~loc v)

(** Is a computation generalizable *)
type generalizable =
  | Generalizable
  | Ungeneralizable

let rec generalizable c =
  match c.Location.thing with
  (* yes *)
  | Rsyntax.Bound _ | Rsyntax.Function _ | Rsyntax.Handler _| Rsyntax.String _ ->
     Generalizable
  | Rsyntax.AMLConstructor (_, cs) | Rsyntax.Tuple cs ->
    if List.for_all (fun c -> generalizable c = Generalizable) cs
    then Generalizable
    else Ungeneralizable
  | Rsyntax.Let (_, c)
  | Rsyntax.LetRec (_, c)
  | Rsyntax.Sequence (_, c) -> generalizable c

  (* no *)
  | Rsyntax.Operation _
  | Rsyntax.With _
  | Rsyntax.Now _
  | Rsyntax.Current _
  | Rsyntax.Lookup _
  | Rsyntax.Update _
  | Rsyntax.Ref _
  | Rsyntax.Assume _
  | Rsyntax.Match _
  | Rsyntax.Ascribe _
  | Rsyntax.IsTypeConstructor _
  | Rsyntax.IsTermConstructor _
  | Rsyntax.EqTypeConstructor _
  | Rsyntax.EqTermConstructor _
  | Rsyntax.Abstract _
  | Rsyntax.Yield _
  | Rsyntax.Apply _
  | Rsyntax.OccursIsTypeAbstraction _
  | Rsyntax.OccursIsTermAbstraction _
  | Rsyntax.OccursEqTypeAbstraction _
  | Rsyntax.OccursEqTermAbstraction _
  | Rsyntax.Context _
  | Rsyntax.Natural _ -> Ungeneralizable

let tt_judgement = function
  | Dsyntax.ML_IsType -> Mlty.IsType
  | Dsyntax.ML_IsTerm -> Mlty.IsTerm
  | Dsyntax.ML_EqType -> Mlty.EqType
  | Dsyntax.ML_EqTerm -> Mlty.EqTerm

let rec tt_abstracted_judgement = function
  | Dsyntax.ML_NotAbstract frm ->
     let frm = tt_judgement frm
     in Mlty.NotAbstract frm
  | Dsyntax.ML_Abstract abstr ->
     let abstr = tt_abstracted_judgement abstr
     in Mlty.Abstract abstr

(* Instantite the bound parameters in a type with the given ones. *)
let rec ml_ty params {Location.thing=t; loc} =
  match t with

  | Dsyntax.ML_Arrow (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Mlty.Arrow (t1, t2)

  | Dsyntax.ML_Prod ts ->
    let ts = List.map (ml_ty params) ts in
    Mlty.Prod ts

  | Dsyntax.ML_TyApply (x, k, ts) ->
    let ts = List.map (ml_ty params) ts in
    Mlty.App (x, k, ts)

  | Dsyntax.ML_Handler (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Mlty.Handler (t1, t2)

  | Dsyntax.ML_Ref t ->
     let t = ml_ty params t in
     Mlty.Ref t

  | Dsyntax.ML_Dynamic t ->
     let t = ml_ty params t in
     Mlty.Dynamic t

  | Dsyntax.ML_Judgement abstr ->
     let abstr = tt_abstracted_judgement abstr
     in Mlty.Judgement abstr

  | Dsyntax.ML_String ->
     Mlty.String

  | Dsyntax.ML_Bound p ->
     Mlty.Param (List.nth params p)

  | Dsyntax.ML_Anonymous ->
     Mlty.fresh_type ()

(* Return a fresh instance of the given schema, with a list of freshly generated parameters. *)
let ml_schema {Location.thing=(Dsyntax.ML_Forall (params, t)); _} =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  let t = ml_ty params t in
  (params, t)

(** Check a TT pattern against an abstracted judgement type and return the processed pattern. *)
let rec check_tt_pattern ~bind_var ({Location.thing=p';loc} as p) t =
  match p' with

  | Dsyntax.Patt_TT_Anonymous ->
     return_located ~loc Pattern.TTAnonymous

  | Dsyntax.Patt_TT_Var x ->
     (* This [add_var] is enclosed by [Tyenv.locally] in [match_case] or [let_clause] *)
     bind_var x (Mlty.Judgement t) >>= fun () ->
     return_located ~loc (Pattern.TTVar x)

  | Dsyntax.Patt_TT_As (p1, p2) ->
     check_tt_pattern ~bind_var p1 t >>= fun p1 ->
     check_tt_pattern ~bind_var p2 t >>= fun p2 ->
     return_located ~loc (Pattern.TTAs (p1, p2))

  | Dsyntax.Patt_TT_Abstraction (xopt, p1, p2) ->
     begin match t with

     | Mlty.NotAbstract t ->
        Mlty.error ~loc (Mlty.UnexpectedJudgementAbstraction t)

     | Mlty.Abstract t ->
        check_tt_pattern ~bind_var p1 (Mlty.NotAbstract Mlty.IsType) >>= fun p1 ->
        begin match xopt with
        | None -> return ()
        | Some x -> bind_var x (Mlty.Judgement (Mlty.NotAbstract Mlty.IsType))
        end >>= fun () ->
        check_tt_pattern ~bind_var p2 t >>= fun p2 ->
        return_located ~loc (Pattern.TTAbstract (xopt, p1, p2))
     end

  (* inferring *)
  | Dsyntax.Patt_TT_Constructor _
  | Dsyntax.Patt_TT_GenAtom _
  | Dsyntax.Patt_TT_IsType _
  | Dsyntax.Patt_TT_IsTerm _
  | Dsyntax.Patt_TT_EqType _
  | Dsyntax.Patt_TT_EqTerm _ ->
     tt_pattern ~bind_var p >>= fun (p, t') ->
     Tyenv.add_equation ~loc (Mlty.Judgement t') (Mlty.Judgement t) >>= fun () ->
     return p


(** Infer the type of a TT pattern. *)
and tt_pattern ~bind_var {Location.thing=p';loc} =
  match p' with

  | Dsyntax.Patt_TT_As (p1, p2) ->
     (* We insist that the first pattern be inferrable *)
     tt_pattern ~bind_var p1 >>= fun (p1, t) ->
     check_tt_pattern ~bind_var p2 t >>= fun p2 ->
     return (locate ~loc (Pattern.TTAs (p1, p2)), t)

  | Dsyntax.Patt_TT_Constructor (c, ps) ->
     Tyenv.lookup_tt_constructor c >>= fun (args, t) ->
     check_tt_args ~bind_var args ps >>= fun ps ->
     return (locate ~loc (Pattern.TTConstructor (c, ps)), Mlty.NotAbstract t)

  | Dsyntax.Patt_TT_GenAtom p ->
     check_tt_pattern ~bind_var p (Mlty.NotAbstract Mlty.IsTerm) >>= fun p ->
     return (p, Mlty.NotAbstract Mlty.IsTerm)

  | Dsyntax.Patt_TT_IsType p ->
     check_tt_pattern ~bind_var p (Mlty.NotAbstract Mlty.IsType) >>= fun p ->
     return (p, Mlty.NotAbstract Mlty.IsType)

  | Dsyntax.Patt_TT_IsTerm (p1, p2) ->
     check_tt_pattern ~bind_var p1 (Mlty.NotAbstract Mlty.IsTerm) >>= fun p1 ->
     check_tt_pattern ~bind_var p2 (Mlty.NotAbstract Mlty.IsType) >>= fun p2 ->
     return (locate ~loc (Pattern.TTIsTerm (p1, p2)), Mlty.NotAbstract Mlty.IsTerm)

  | Dsyntax.Patt_TT_EqType (p1, p2) ->
     check_tt_pattern ~bind_var p1 (Mlty.NotAbstract Mlty.IsType) >>= fun p1 ->
     check_tt_pattern ~bind_var p2 (Mlty.NotAbstract Mlty.IsType) >>= fun p2 ->
     return (locate ~loc (Pattern.TTEqType (p1, p2)), Mlty.NotAbstract Mlty.EqType)

  | Dsyntax.Patt_TT_EqTerm (p1, p2, p3) ->
     check_tt_pattern ~bind_var p1 (Mlty.NotAbstract Mlty.IsTerm) >>= fun p1 ->
     check_tt_pattern ~bind_var p2 (Mlty.NotAbstract Mlty.IsTerm) >>= fun p2 ->
     check_tt_pattern ~bind_var p3 (Mlty.NotAbstract Mlty.IsType) >>= fun p3 ->
     return (locate ~loc (Pattern.TTEqTerm (p1, p2, p3)), Mlty.NotAbstract Mlty.EqTerm)

  | Dsyntax.Patt_TT_Abstraction (x, p1, p2) ->
     check_tt_pattern ~bind_var p1 (Mlty.NotAbstract Mlty.IsType) >>= fun p1 ->
     tt_pattern ~bind_var p2 >>= fun (p2, t) ->
     return (locate ~loc (Pattern.TTAbstract (x, p1, p2)), Mlty.Abstract t)

  (* non-inferrable *)
  | Dsyntax.Patt_TT_Anonymous
  | Dsyntax.Patt_TT_Var _ ->
     Mlty.error ~loc Mlty.UnknownJudgementForm

and check_tt_args ~bind_var args ps =
  let rec fold ps_out args ps =
    begin match (ps, args) with

    | [], [] -> return (List.rev ps_out)

    | p :: ps, arg :: args ->
       check_tt_pattern ~bind_var p arg >>= fun p ->
       fold (p :: ps_out) args ps

    | [], _::_
    | _::_, [] ->
       (* desugar already checked arities *)
       assert false
    end
  in
  fold [] args ps


(** Infer the type of a pattern *)
let rec pattern ~bind_var {Location.thing=p;loc} =
  match p with
  | Dsyntax.Patt_Anonymous ->
     return (locate ~loc Pattern.Anonymous, Mlty.fresh_type ())

  | Dsyntax.Patt_Var x ->
     let t = Mlty.fresh_type () in
     bind_var x t >>= fun () ->
     return (locate ~loc (Pattern.Var x), t)

  | Dsyntax.Patt_As (p1, p2) ->
     pattern ~bind_var p1 >>= fun (p1, t1) ->
     check_pattern ~bind_var p2 t1 >>= fun p2 ->
     return (locate ~loc (Pattern.As (p1, p2)), t1)

  | Dsyntax.Patt_Judgement p ->
     tt_pattern ~bind_var p >>= fun (p, t) ->
     return (locate ~loc (Pattern.Judgement p), Mlty.Judgement t)

  | Dsyntax.Patt_Constr (c, ps) ->
    Tyenv.lookup_aml_constructor c >>= fun (ts, out) ->
    let rec fold qs ps ts =
      match ps, ts with
      | [], [] ->
         let qs = List.rev qs in
         return (locate ~loc (Pattern.AMLConstructor (c, qs)), out)
      | p::ps, t::ts ->
        check_pattern ~bind_var p t >>= fun q ->
        fold (q::qs) ps ts
      | [], _::_ | _::_, [] ->
         assert false
    in
    fold [] ps ts

  | Dsyntax.Patt_Tuple ps ->
    let rec fold qs ts = function
      | [] ->
         let qs = List.rev qs
         and ts = List.rev ts in
         return (locate ~loc (Pattern.Tuple qs), Mlty.Prod ts)
      | p :: ps ->
         pattern ~bind_var p >>= fun (q, t) ->
         fold (q :: qs) (t :: ts) ps
    in
    fold [] [] ps

and check_pattern ~bind_var ({Location.thing=p'; loc} as p) t =
  match p' with
  | Dsyntax.Patt_Anonymous ->
     return_located ~loc Pattern.Anonymous

  | Dsyntax.Patt_Var x ->
     bind_var x t >>= fun () ->
     return_located ~loc (Pattern.Var x)

  | Dsyntax.Patt_As (p1, p2) ->
     check_pattern ~bind_var p1 t >>= fun p1 ->
     check_pattern ~bind_var p2 t >>= fun p2 ->
     return_located ~loc (Pattern.As (p1, p2))

  | Dsyntax.Patt_Judgement p ->
     begin match t with

     | Mlty.Judgement t ->
        check_tt_pattern ~bind_var p t >>= fun p ->
        return_located ~loc (Pattern.Judgement p)

     | Mlty.String | Mlty.Meta _ | Mlty.Param _ | Mlty.Prod _ | Mlty.Arrow _
     | Mlty.Handler _ | Mlty.App _ | Mlty.Ref _ | Mlty.Dynamic _ ->
          Mlty.error ~loc (Mlty.UnexpectedJudgement t)
     end

  | Dsyntax.Patt_Tuple ps ->
     begin match t with
     | Mlty.Prod ts when (List.length ps = List.length ts) ->
        let rec fold ps_out ps ts =
          match ps, ts with
          | [], [] ->
             let ps_out = List.rev ps_out in
             return_located ~loc (Pattern.Tuple ps_out)
          | p :: ps, t :: ts ->
             check_pattern ~bind_var p t >>= fun p ->
             fold (p :: ps_out) ps ts
          | [], _::_ | _::_, [] -> assert false
        in
        fold [] ps ts

     | Mlty.Prod _ | Mlty.Judgement _  | Mlty.String | Mlty.Meta _ | Mlty.Param _
     | Mlty.Arrow _ | Mlty.Handler _ | Mlty.App _ | Mlty.Ref _ | Mlty.Dynamic _ ->
        pattern ~bind_var p >>= fun (p, t') ->
        Tyenv.add_equation ~loc t' t >>= fun () ->
        return p
     end


  | Dsyntax.Patt_Constr _ ->
     pattern ~bind_var p >>= fun (p, t') ->
     Tyenv.add_equation ~loc:p.Location.loc t' t >>= fun () ->
     return p

let rec comp ({Location.thing=c; loc} : Dsyntax.comp) : (Rsyntax.comp * Mlty.ty) Tyenv.tyenvM =
  match c with
  | Dsyntax.Bound k ->
    Tyenv.lookup_var k >>= fun t ->
    return (locate ~loc (Rsyntax.Bound k), t)

  | Dsyntax.Function (x, annot, c) ->
     let a =
       begin
         match annot with
         | Dsyntax.Arg_annot_none -> Mlty.fresh_type ()
         | Dsyntax.Arg_annot_ty t -> ml_ty [] t
       end
     in
     Tyenv.locally_add_var x a
     begin
       comp c >>= fun (c, b) ->
       return (locate ~loc (Rsyntax.Function (x, c)), Mlty.Arrow (a, b))
     end

  | Dsyntax.Handler h ->
     handler ~loc h >>= fun (h, t) ->
     return (locate ~loc (Rsyntax.Handler h), t)

  | Dsyntax.TT_Constructor (c, cs) ->
    Tyenv.lookup_tt_constructor c >>= fun (ts, out) ->
    let rec fold cs_out cs ts =
      match cs, ts with
      | [], [] ->
        let cs_out = List.rev cs_out in
        let e =
          begin match out with
          | Mlty.IsType -> Rsyntax.IsTypeConstructor (c, cs_out)
          | Mlty.IsTerm -> Rsyntax.IsTermConstructor (c, cs_out)
          | Mlty.EqType -> Rsyntax.EqTypeConstructor (c, cs_out)
          | Mlty.EqTerm -> Rsyntax.EqTermConstructor (c, cs_out)
          end
        in
        return (locate ~loc e, Mlty.Judgement (Mlty.NotAbstract out))
      | c :: cs, t :: ts ->
        check_comp c (Mlty.Judgement t) >>= fun c ->
        fold (c :: cs_out) cs ts
      | [], _::_ | _::_, [] -> assert false
    in
    fold [] cs ts

  | Dsyntax.AMLConstructor (c, cs) ->
    Tyenv.lookup_aml_constructor c >>= fun (ts, out) ->
    let tcs = List.combine ts cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        return (locate ~loc (Rsyntax.AMLConstructor (c, cs)), out)
      | (t, c) :: tcs ->
        check_comp c t >>= fun c ->
        fold (c :: cs) tcs
    in
    fold [] tcs

  | Dsyntax.Tuple cs ->
    let rec fold annot ts = function
      | [] ->
        let ts = List.rev ts
        and cs = List.rev annot in
        return (locate ~loc (Rsyntax.Tuple cs), Mlty.Prod ts)
      | c :: cs ->
        comp c >>= fun (c, t) ->
        fold (c :: annot) (t :: ts) cs
    in
    fold [] [] cs

  | Dsyntax.Operation (op, cs) ->
    Tyenv.lookup_op op >>= fun (expected, out) ->
    let tcs = List.combine expected cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        return (locate ~loc (Rsyntax.Operation (op, cs)), out)
      | (t, c) :: tcs ->
        check_comp c t >>= fun c ->
        fold (c :: cs) tcs
    in
    fold [] tcs

  | Dsyntax.With (h, c) ->
    comp h >>= fun (h, th) ->
    Tyenv.as_handler ~loc:h.Location.loc th >>= fun (a, b) ->
    check_comp c a >>= fun c ->
    return (locate ~loc (Rsyntax.With (h, c)), b)

  | Dsyntax.Let (clauses, c) ->
     let_clauses ~locally:true
       clauses (comp c) >>= fun (clauses, (c, t)) ->
         return (locate ~loc (Rsyntax.Let (clauses, c)), t)

  | Dsyntax.LetRec (clauses, c) ->
     letrec_clauses
       clauses (comp c) >>= fun (clauses, (c, t)) ->
         return (locate ~loc (Rsyntax.LetRec (clauses, c)), t)

  | Dsyntax.MLAscribe (c, sch) ->
      let sch = ml_schema sch in
      comp c >>= fun (c, t) ->
       begin
         match generalizable c with
         | Generalizable ->
            Tyenv.get_context >>= fun known_context ->
            Tyenv.generalizes_to ~loc:c.Location.loc ~known_context t sch
         | Ungeneralizable ->
            begin
              match sch with
              | ([], tsch) ->
                 Tyenv.add_equation ~loc:c.Location.loc t tsch
              | (_::_, _) ->
                 Mlty.error ~loc:c.Location.loc Mlty.ValueRestriction
            end
       end >>= fun () -> return (c, t)

  | Dsyntax.Now (x, c1, c2) ->
     comp x >>= fun (x, tx) ->
     Tyenv.as_dynamic ~loc:x.Location.loc tx >>= fun tx ->
     check_comp c1 tx >>= fun c1 ->
     comp c2 >>= fun (c2, t) ->
     return (locate ~loc (Rsyntax.Now (x, c1, c2)), t)

  | Dsyntax.Current c ->
     comp c >>= fun (c, t) ->
     Tyenv.as_dynamic ~loc:c.Location.loc t >>= fun t ->
     return (locate ~loc (Rsyntax.Current c), t)

  | Dsyntax.Lookup c ->
    comp c >>= fun (c, t) ->
    Tyenv.as_ref ~loc:c.Location.loc t >>= fun t ->
    return (locate ~loc (Rsyntax.Lookup c), t)

  | Dsyntax.Update (c1, c2) ->
    comp c1 >>= fun (c1, t1) ->
    Tyenv.as_ref ~loc:c1.Location.loc t1 >>= fun t ->
    check_comp c2 t >>= fun c2 ->
    return (locate ~loc (Rsyntax.Update (c1, c2)), Mlty.unit_ty)

  | Dsyntax.Ref c ->
    comp c >>= fun (c, t) ->
    return (locate ~loc (Rsyntax.Ref c), Mlty.Ref t)

  | Dsyntax.Sequence (c1, c2) ->
    comp c1 >>= fun (c1, _) ->
    (* TODO warn if not unit? *)
    comp c2 >>= fun (c2, t) ->
    return (locate ~loc (Rsyntax.Sequence (c1, c2)), t)

  | Dsyntax.Assume ((x, c1), c2) ->
     let t = (Mlty.Judgement (Mlty.NotAbstract Mlty.IsType)) in
     check_comp c1 t >>= fun c1 ->
     Tyenv.locally_add_var x t
     begin
       comp c2 >>= fun (c2, u) ->
       return (locate ~loc (Rsyntax.Assume ((x, c1), c2)), u)
     end

  | Dsyntax.Match (c, cases) ->
    comp c >>= fun (c, tc) ->
    match_cases ~loc tc cases >>= fun (cases, t) ->
    return (locate ~loc (Rsyntax.Match (c, cases)), t)

  | Dsyntax.Ascribe (c1, c2) ->
     let t1 = Mlty.Judgement (Mlty.NotAbstract Mlty.IsTerm)
     and t2 = Mlty.Judgement (Mlty.NotAbstract Mlty.IsType) in
     check_comp c1 t1 >>= fun c1 ->
     check_comp c2 t2 >>= fun c2 ->
     return (locate ~loc (Rsyntax.Ascribe (c1, c2)), t1)

  | Dsyntax.Abstract (x, copt, c) ->
    begin match copt with
      | Some ct -> check_comp ct (Mlty.Judgement (Mlty.NotAbstract Mlty.IsType)) >>= fun ct -> return (Some ct)
      | None -> return None
    end >>= fun copt ->
    Tyenv.locally_add_var
      x
      (Mlty.Judgement (Mlty.NotAbstract Mlty.IsTerm))
      begin
        comp c >>= fun (c,t) ->
        begin match t with
        | Mlty.Judgement t ->
           let c = locate ~loc (Rsyntax.Abstract (x, copt, c))
           and t = Mlty.Judgement (Mlty.Abstract t) in
           return (c, t)
        | Mlty.(String | Meta _ | Param _ | Prod _ | Arrow _ | Handler _ | App _ | Ref _|Dynamic _) as t ->
           Mlty.error ~loc (Mlty.JudgementExpected t)
        end
      end

  | Dsyntax.Apply (c1, c2) ->
     comp c1 >>= fun (c1, t1) ->
     comp c2 >>= fun (c2, t2) ->
     let out = Mlty.fresh_type () in
     Tyenv.add_application ~loc t1 t2 out >>= fun () ->
     return (locate ~loc (Rsyntax.Apply (c1, c2)), out)

  | Dsyntax.Yield c ->
    Tyenv.lookup_continuation >>= fun (a, b) ->
    check_comp c a >>= fun c ->
    return (locate ~loc (Rsyntax.Yield c), b)

  | Dsyntax.String s -> return (locate ~loc (Rsyntax.String s), Mlty.String)

  | Dsyntax.Occurs (c1, c2) ->
     let t = Mlty.Judgement (Mlty.NotAbstract Mlty.IsTerm) in
     check_comp c1 t >>= fun c1 ->
     comp c2 >>= fun (c2, t2) ->
     begin match t2 with

     | Mlty.Judgement abstr ->

        Tyenv.predefined_type Name.Predefined.option
          [Mlty.Judgement (Mlty.NotAbstract Mlty.IsType)] >>= fun t ->

        let rec form = function
          | Mlty.Abstract u -> form u
          | Mlty.NotAbstract frm -> frm
        in
        begin match form abstr with
        | Mlty.IsType ->
           return (locate ~loc (Rsyntax.OccursIsTypeAbstraction (c1, c2)), t)
        | Mlty.IsTerm ->
           return (locate ~loc (Rsyntax.OccursIsTermAbstraction (c1, c2)), t)
        | Mlty.EqType ->
           return (locate ~loc (Rsyntax.OccursEqTypeAbstraction (c1, c2)), t)
        | Mlty.EqTerm ->
           return (locate ~loc (Rsyntax.OccursEqTermAbstraction (c1, c2)), t)
        end

     | Mlty.(String | Meta _ | Param _ | Prod _ | Arrow _
     | Handler _ | App _ | Ref _ | Dynamic _) ->
        Mlty.error ~loc:c2.Location.loc (Mlty.JudgementExpected t2)
     end


  | Dsyntax.Context c ->
     let t = Mlty.Judgement (Mlty.NotAbstract Mlty.IsTerm) in
     check_comp c t >>= fun c ->
     Tyenv.predefined_type Name.Predefined.list [t] >>= fun t ->
     return (locate ~loc (Rsyntax.Context c), t)

  | Dsyntax.Natural c ->
     let t = Mlty.Judgement (Mlty.NotAbstract Mlty.IsTerm) in
     check_comp c t >>= fun c ->
     return (locate ~loc (Rsyntax.Natural c), Mlty.Judgement (Mlty.NotAbstract Mlty.EqType))

and check_comp c t =
  comp c >>= fun (c, t') ->
  Tyenv.add_equation ~loc:c.Location.loc t' t >>= fun () ->
  return c

and handler ~loc {Dsyntax.handler_val=handler_val;handler_ops;handler_finally} =
  let input = Mlty.fresh_type () in
  begin match handler_val with
    | [] -> return ([], input)
    | _ :: _ -> match_cases ~loc input handler_val
  end >>= fun (handler_val, output) ->
  begin match handler_finally with
    | [] -> return ([], output)
    | _ :: _ -> match_cases ~loc output handler_finally
  end >>= fun (handler_finally, final) ->
  let rec fold ops = function
    | [] ->
      return (List.fold_left (fun acc (x, v) -> Name.IdentMap.add x v acc) Name.IdentMap.empty ops)
    | (op, cases) :: rem ->
      match_op_cases op cases output >>= fun cases ->
      fold ((op, cases) :: ops) rem
  in
  fold [] (Name.IdentMap.bindings handler_ops) >>= fun handler_ops ->
  return ({Rsyntax.handler_val=handler_val;handler_ops;handler_finally}, Mlty.Handler (input, final))

and match_case p t c =
  Tyenv.locally
    begin
      check_pattern ~bind_var:Tyenv.add_var p t >>= fun p ->
      comp c >>= fun (c, tc) ->
      return (p, c, tc)
    end

and check_match_case p tp c tc =
  Tyenv.locally
    begin
      check_pattern ~bind_var:Tyenv.add_var p tp >>= fun p ->
      check_comp c tc >>= fun c ->
      return (p, c)
    end

and match_cases ~loc t = function
  | [] ->
     return ([], Mlty.fresh_type ())

  | (p1, c1) :: cases ->
     match_case p1 t c1 >>= fun (p1, c1, out) ->
     let rec fold cases = function
       | [] ->
          let cases = List.rev cases in
          return (cases, out)
       | (p, c) :: others ->
          check_match_case p t c out >>= fun (p, c) ->
          fold ((p, c) :: cases) others
      in
      fold [(p1, c1)] cases

and match_op_cases op cases t_out =
  Tyenv.op_cases
    op ~output:t_out
    (fun ts ->
      let rec fold_cases cases = function
        | [] -> return (List.rev cases)
        | (ps, popt, c) :: rem ->
           let rec fold_args ps_out ps ts =
             match ps, ts with
             | [], [] ->
                let ps_out = List.rev ps_out in
                begin match popt with
                | None -> return None
                | Some p ->
                   check_tt_pattern ~bind_var:Tyenv.add_var p (Mlty.NotAbstract Mlty.IsType) >>= fun p ->
                   return (Some p)
                end >>= fun popt ->
                check_comp c t_out >>= fun c ->
                return (ps_out, popt, c)
             | p::ps, t::ts ->
                check_pattern ~bind_var:Tyenv.add_var p t >>= fun p ->
                fold_args (p :: ps_out) ps ts
             | [], _::_ | _::_, [] ->
                assert false
           in
           Tyenv.locally (fold_args [] ps ts) >>= fun case ->
           fold_cases (case :: cases) rem
      in
      fold_cases [] cases)

and let_clauses
  :  'a . locally:bool -> Dsyntax.let_clause list -> 'a Tyenv.tyenvM ->
          (Rsyntax.let_clause list * 'a) Tyenv.tyenvM
  = fun ~locally clauses_in m ->
  let rec fold_rhs cts = function
    | [] -> return (List.rev cts)
    | Dsyntax.Let_clause (p, annot, c) :: clauses_in ->
       comp c >>= fun (c, t) ->
       fold_rhs ((p, annot, c, t) :: cts) clauses_in
  in

  let rec fold_lhs clauses_out = function
    | [] -> return (List.rev clauses_out)

    | (p, annot, c, t) :: clauses_in ->
       (* We explicitly save the old context because [check_pattern] binds the
          variables that we want to generalise, but [Tyenv.generalize] needs to
          know about the [old_context]. *)
       Tyenv.get_context >>= fun old_context ->
       Tyenv.record_vars (check_pattern ~bind_var:Tyenv.record_var p t) >>= fun (xts, p) ->
       begin match generalizable c with

       | Generalizable ->
          begin match annot with
          | Dsyntax.Let_annot_schema sch ->
             let sch = ml_schema sch in
             Tyenv.generalizes_to ~loc:c.Location.loc ~known_context:old_context t sch

          | Dsyntax.Let_annot_none -> return ()
          end >>= fun () ->

          let rec fold xss = function
            | [] -> fold_lhs (Rsyntax.Let_clause (List.rev xss, p, c) :: clauses_out) clauses_in
            | (x,t) :: xts ->
               Tyenv.generalize ~known_context:old_context t >>= fun sch ->
               Tyenv.add_let x sch >>= fun () ->
               fold ((x,sch) :: xss) xts
          in
          fold [] xts

       | Ungeneralizable ->
          begin match annot with
          | Dsyntax.Let_annot_schema sch ->
             let sch = ml_schema sch in
             begin match sch with
             | ([], tsch) -> Tyenv.add_equation ~loc:c.Location.loc t tsch
             | (_::_, _) -> Mlty.error ~loc:c.Location.loc Mlty.ValueRestriction
             end
          | Dsyntax.Let_annot_none -> return ()
          end >>= fun () ->
          let rec fold xss = function
            | [] -> fold_lhs (Rsyntax.Let_clause (List.rev xss, p, c) :: clauses_out) clauses_in
            | (x,t) :: xts ->
               Tyenv.ungeneralize t >>= fun sch ->
               Tyenv.add_let x sch >>= fun () ->
               fold ((x,sch) :: xss) xts
          in
          fold [] xts
       end
  in
  fold_rhs [] clauses_in >>= fun pacts ->
  (if locally then Tyenv.locally else fun mojo -> mojo)
    begin
      fold_lhs [] pacts >>= fun clauses ->
      m >>= fun x ->
      return (clauses, x)
    end

and letrec_clauses
  :  'a . Dsyntax.letrec_clause list -> 'a Tyenv.tyenvM ->
          (Rsyntax.letrec_clause list * 'a) Tyenv.tyenvM
  = fun fycs m ->

  Tyenv.get_context >>= fun old_context ->

  let rec bind_functions acc = function
    | [] -> return (List.rev acc)

    | Dsyntax.Letrec_clause (f, (y, a), annot, c) :: rem ->
       let a =
         begin
           match a with
           | Dsyntax.Arg_annot_none -> Mlty.fresh_type ()
           | Dsyntax.Arg_annot_ty t -> ml_ty [] t
         end
       and b = Mlty.fresh_type () in
       begin
         match annot with
         | Dsyntax.Let_annot_none ->
            Tyenv.ungeneralize (Mlty.Arrow (a, b)) >>= fun sch ->
            return (sch, None)
         | Dsyntax.Let_annot_schema sch ->
            let sch = ml_schema sch in
            return (sch, Some sch)
       end >>= fun (sch, schopt) ->
       Tyenv.add_let f sch >>= fun () ->
         bind_functions ((f, schopt, y, a, c, b) :: acc) rem
  in

  let rec check_bodies acc = function
    | [] -> return (List.rev acc)

    | (f, schopt, y, a, c, b) :: rem ->
       Tyenv.locally_add_var y a (check_comp c b) >>= fun c ->
       check_bodies ((f, schopt, y, a, c, b) :: acc) rem
  in

  let rec generalize_funs acc = function
    | [] -> return (List.rev acc)

    | (f, Some sch, y, a, c, b) :: rem ->
       let t = Mlty.Arrow (a, b) in
       Tyenv.generalizes_to ~loc:c.Location.loc t ~known_context:old_context sch >>= fun () ->
       generalize_funs (Rsyntax.Letrec_clause (f, y, sch, c) :: acc) rem

    | (f, None, y, a, c, b) :: rem ->
       let t = Mlty.Arrow (a, b) in
       Tyenv.generalize ~known_context:old_context t >>= fun sch ->
       generalize_funs (Rsyntax.Letrec_clause (f, y, sch, c) :: acc) rem

  in

  bind_functions [] fycs >>=
  check_bodies []  >>=
  generalize_funs [] >>= fun clauses ->
  m >>= fun x ->
  return (clauses, x)


let top_handler ~loc lst =
  let rec fold cases = function
    | [] -> return (List.rev cases)
    | (op, (xs, yopt, c)) :: lst ->
      Tyenv.lookup_op op >>= fun (argts, out) ->
      let xts = List.combine xs argts in
      let rec bind = function
        | [] ->
          let bindy m = match yopt with
            | Some y ->
               Tyenv.predefined_type
                 Name.Predefined.option [Mlty.Judgement (Mlty.NotAbstract Mlty.IsType)] >>= fun jdg_opt ->
               Tyenv.locally_add_var y jdg_opt m
            | None -> m
          in
          bindy (check_comp c out)
        | (x, t) :: xts ->
          Tyenv.locally_add_var x t (bind xts)
      in
      bind xts >>= fun c ->
      fold ((op, (xs, yopt, c)) :: cases) lst
  in
  fold [] lst

let add_tydef (t, (params, def)) =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  match def with

    | Dsyntax.ML_Alias t' ->
       let t' = ml_ty params t' in
       Tyenv.add_tydef t (Mlty.Alias (params, t'))

    | Dsyntax.ML_Sum constructors ->
       let constructors = List.map (fun (c, ts) -> c, List.map (ml_ty params) ts) constructors in
       Tyenv.add_tydef t (Mlty.Sum (params, constructors))

let rec toplevel ({Location.thing=c; loc} : Dsyntax.toplevel) =
  match c with
  (* Desugar is the only place where recursion/nonrecursion matters *)
  | Dsyntax.DefMLType tydefs ->
     let rec fold = function
       | [] -> return_located ~loc (Rsyntax.DefMLType tydefs)
       | tydef :: tydefs -> add_tydef tydef >>= fun () -> fold tydefs
     in
     fold tydefs

  | Dsyntax.DefMLTypeRec tydefs ->
     let rec fold = function
       | [] -> return_located ~loc (Rsyntax.DefMLTypeRec tydefs)
       | tydef :: tydefs -> add_tydef tydef >>= fun () -> fold tydefs
     in
     fold tydefs

  | Dsyntax.DeclOperation (op, (tys_in, ty_out)) ->
    let tys_in = List.map (ml_ty []) tys_in in
    let ty_out = ml_ty [] ty_out in
    Tyenv.add_operation op (tys_in, ty_out) >>= fun () ->
    return_located ~loc (Rsyntax.DeclOperation (op, (tys_in, ty_out)))

  | Dsyntax.DeclExternal (x, sch, s) ->
     let sch = ml_schema sch in
     Tyenv.add_let x sch >>= fun () ->
     return_located ~loc (Rsyntax.DeclExternal (x, sch, s))

  | Dsyntax.TopHandle lst ->
     top_handler ~loc lst >>= fun lst ->
     return_located ~loc (Rsyntax.TopHandle lst)

  | Dsyntax.TopLet clauses ->
     let_clauses ~locally:false clauses (return ()) >>= fun (clauses, ()) ->
     return_located ~loc (Rsyntax.TopLet clauses)

  | Dsyntax.TopLetRec clauses ->
     letrec_clauses clauses (return ()) >>= fun (clauses, ()) ->
     return_located ~loc (Rsyntax.TopLetRec clauses)

  | Dsyntax.TopDynamic (x, annot, c) ->
     comp c >>= fun (c, t) ->
     begin match annot with
     | Dsyntax.Arg_annot_none ->
        Tyenv.ungeneralize (Mlty.Dynamic t) >>= fun sch ->
        return (c, sch)
     | Dsyntax.Arg_annot_ty t' ->
        let t' = ml_ty [] t' in
        Tyenv.add_equation ~loc:c.Location.loc t t' >>= fun () ->
        Tyenv.ungeneralize (Mlty.Dynamic t') >>= fun sch ->
        return (c, sch)
     end >>= fun (c, sch) ->
     Tyenv.add_let x sch >>= fun () ->
     return_located ~loc (Rsyntax.TopDynamic (x, sch, c))

  | Dsyntax.TopNow (x, c) ->
       comp x >>= fun (x, tx) ->
       Tyenv.as_dynamic ~loc:x.Location.loc tx >>= fun tx ->
       check_comp c tx >>= fun c ->
       return_located ~loc (Rsyntax.TopNow (x, c))

  | Dsyntax.TopDo c ->
     comp c >>= fun (c, _) ->
     return_located ~loc (Rsyntax.TopDo c)

  | Dsyntax.TopFail c ->
     comp c >>= fun (c, _) ->
     return_located ~loc (Rsyntax.TopFail c)

  | Dsyntax.Verbosity v ->
    return_located ~loc (Rsyntax.Verbosity v)

  | Dsyntax.Included fcs ->
    let rec fold_files fcs = function
      | [] -> return (List.rev fcs)
      | (f, cs) :: rem ->
         let rec fold cs_out = function
           | [] -> return (List.rev cs_out)
           | c :: cs ->
              toplevel c >>= fun c ->
              fold (c :: cs_out) cs
         in
         fold [] cs >>= fun cs ->
         fold_files ((f, cs) :: fcs) rem
    in
    fold_files [] fcs >>= fun fcs ->
    return_located ~loc (Rsyntax.Included fcs)

let toplevel env c = Tyenv.run env (toplevel c)
