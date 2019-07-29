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
  | (Rsyntax.Bound _ | Rsyntax.Value _ | Rsyntax.Function _
    | Rsyntax.Handler _| Rsyntax.String _) ->
     Generalizable
  | Rsyntax.MLConstructor (_, cs) | Rsyntax.Tuple cs ->
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
  | Rsyntax.BoundaryAscribe _
  | Rsyntax.TypeAscribe _
  | Rsyntax.TTConstructor _
  | Rsyntax.Abstract _
  | Rsyntax.Substitute _
  | Rsyntax.Yield _
  | Rsyntax.Apply _
  | Rsyntax.Occurs _
  | Rsyntax.Convert _
  | Rsyntax.Context _
  | Rsyntax.Natural _
  | Rsyntax.MLBoundary _
  -> Ungeneralizable

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

  | Dsyntax.ML_Apply (pth, ts) ->
    let ts = List.map (ml_ty params) ts in
    Mlty.Apply (pth, ts)

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

  | Dsyntax.ML_Judgement ->
     Mlty.Judgement

  | Dsyntax.ML_Boundary ->
     Mlty.Boundary

  | Dsyntax.ML_String ->
     Mlty.String

  | Dsyntax.ML_Bound (Path.Index (_, i)) ->
     Mlty.Param (List.nth params i)

  | Dsyntax.ML_Anonymous ->
     Mlty.fresh_type ()

(* Return a fresh instance of the given schema, with a list of freshly generated parameters. *)
let ml_schema {Location.thing=(Dsyntax.ML_Forall (params, t)); _} =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  let t = ml_ty params t in
  (params, t)

let check_boundary_pattern {Location.thing=p';loc} =
  failwith "type-checking of boundary patterns not implemented"

(** Infer the type of a pattern *)
let rec infer_pattern {Location.thing=p;loc} =
  match p with
  | Dsyntax.Patt_Anonymous ->
     return (locate ~loc Rsyntax.Patt_Anonymous, Mlty.fresh_type (), [])

  | Dsyntax.Patt_Var x ->
     let t = Mlty.fresh_type () in
     return (locate ~loc Rsyntax.Patt_Var, t, [(x, t)])

  | Dsyntax.Patt_As (p1, p2) ->
     infer_pattern p1 >>= fun (p1, t1, xts1) ->
     check_pattern p2 t1 >>= fun (p2, xts2) ->
     return (locate ~loc (Rsyntax.Patt_As (p1, p2)), t1, xts1 @ xts2)

  | Dsyntax.Patt_MLConstructor (tag, ps) ->
    Tyenv.lookup_ml_constructor tag >>= fun (tag_id, ts, out) ->
    check_patterns ps ts >>= fun (ps, xts) ->
    return (locate ~loc (Rsyntax.Patt_MLConstructor (tag_id, ps)), out, xts)

  | Dsyntax.Patt_TTConstructor (c, ps) ->
     Tyenv.lookup_tt_constructor c >>= fun c ->
     let ts = List.map (fun _ -> Mlty.Judgement) ps in
     check_patterns ps ts >>= fun (ps, xts) ->
     return (locate ~loc (Rsyntax.Patt_TTConstructor (c, ps)), Mlty.Judgement, xts)

  | Dsyntax.Patt_GenAtom p ->
     check_pattern p Mlty.Judgement >>= fun (p, xts) ->
     return (locate ~loc (Rsyntax.Patt_GenAtom p), Mlty.Judgement, xts)

  | Dsyntax.Patt_IsType p ->
     check_pattern p Mlty.Judgement >>= fun (p, xts) ->
     return (locate ~loc (Rsyntax.Patt_IsType p), Mlty.Judgement, xts)

  | Dsyntax.Patt_IsTerm (p1, p2) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     return (locate ~loc (Rsyntax.Patt_IsTerm (p1, p2)), Mlty.Judgement, xts1 @ xts2)

  | Dsyntax.Patt_EqType (p1, p2) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     return (locate ~loc (Rsyntax.Patt_EqType (p1, p2)), Mlty.Judgement, xts1 @ xts2)

  | Dsyntax.Patt_EqTerm (p1, p2, p3) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     check_pattern p3 Mlty.Judgement >>= fun (p3, xts3) ->
     return (locate ~loc (Rsyntax.Patt_EqTerm (p1, p2, p3)), Mlty.Judgement, xts1 @ xts2 @ xts3)

  | Dsyntax.Patt_BoundaryIsType ->
     return (locate ~loc (Rsyntax.Patt_BoundaryIsType), Mlty.Boundary, [])

  | Dsyntax.Patt_BoundaryIsTerm p ->
     check_pattern p Mlty.Judgement >>= fun (p, xts) ->
     return (locate ~loc (Rsyntax.Patt_BoundaryIsTerm p), Mlty.Boundary, xts)

  | Dsyntax.Patt_BoundaryEqType (p1, p2) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     return (locate ~loc (Rsyntax.Patt_BoundaryEqType (p1, p2)), Mlty.Boundary, xts1 @ xts2)

  | Dsyntax.Patt_BoundaryEqTerm (p1, p2, p3) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     check_pattern p3 Mlty.Judgement >>= fun (p3, xts3) ->
     return (locate ~loc (Rsyntax.Patt_BoundaryEqTerm (p1, p2, p3)), Mlty.Boundary, xts1 @ xts2 @ xts3)

  | Dsyntax.Patt_Abstraction (xopt, p1, p2) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     infer_pattern p2 >>= fun (p2, t2, xts2) ->
     (** XXX verify whether [t2] is guaranteed to be normalized *)
     begin match t2 with

     | Mlty.(Judgement | Boundary) ->
        let xts2 =
          match xopt with
          | None -> xts2
          | Some x -> (x, Mlty.Judgement) :: xts2
        in
        return (locate ~loc (Rsyntax.Patt_Abstract (xopt, p1, p2)), Mlty.Judgement, xts1 @ xts2)

     | Mlty.Meta _ -> Mlty.error ~loc Mlty.UninferrableExpression

     | Mlty.(String | Param _ | Prod _ | Arrow _ | Handler _ | Apply _ | Ref _| Dynamic _) as t ->
        Mlty.error ~loc (Mlty.JudgementOrBoundaryExpected t)
     end

  | Dsyntax.Patt_Tuple ps ->
    let rec fold qs ts xts = function
      | [] ->
         let qs = List.rev qs
         and ts = List.rev ts in
         return (locate ~loc (Rsyntax.Patt_Tuple qs), Mlty.Prod ts, xts)
      | p :: ps ->
         infer_pattern p >>= fun (q, t, p_xts) ->
         fold (q :: qs) (t :: ts) (xts @ p_xts) ps
    in
    fold [] [] [] ps


and check_pattern ({Location.thing=p'; loc} as p) t =
  match p' with
  | Dsyntax.Patt_Anonymous ->
     return (locate ~loc Rsyntax.Patt_Anonymous, [])

  | Dsyntax.Patt_Var x ->
     return (locate ~loc Rsyntax.Patt_Var, [(x, t)])

  | Dsyntax.Patt_As (p1, p2) ->
     check_pattern p1 t >>= fun (p1, xts1) ->
     check_pattern p2 t >>= fun (p2, xts2) ->
     return (locate ~loc (Rsyntax.Patt_As (p1, p2)), xts1 @ xts2)

  | Dsyntax.Patt_Tuple ps ->
     begin match t with
     | Mlty.Prod ts when (List.length ps = List.length ts) ->
        check_patterns ps ts >>= fun (ps, xts) ->
        return (locate ~loc (Rsyntax.Patt_Tuple ps), xts)

     | Mlty.(Prod _ | Judgement | Boundary | String | Meta _ | Param _ |
             Arrow _ | Handler _ | Apply _ | Ref _ | Dynamic _) ->
        infer_pattern p >>= fun (p, t', xts) ->
        Tyenv.add_equation ~loc t' t >>= fun () ->
        return (p, xts)
     end

  | Dsyntax.(Patt_MLConstructor _ | Patt_TTConstructor _ |
             Patt_BoundaryIsType | Patt_BoundaryIsTerm _ | Patt_BoundaryEqType _ | Patt_BoundaryEqTerm _ |
             Patt_GenAtom _ | Patt_IsType _ | Patt_IsTerm _ | Patt_EqType _ | Patt_EqTerm _ | Patt_Abstraction _)->
     infer_pattern p >>= fun (p, t', xts) ->
     Tyenv.add_equation ~loc:p.Location.loc t' t >>= fun () ->
     return (p, xts)

and check_patterns ps ts =
  let rec fold ps_out xts ps ts =
    match ps, ts with
    | [], [] ->
       let ps_out = List.rev ps_out in
       return (ps_out, xts)
    | p::ps, t::ts ->
       check_pattern p t >>= fun (p_out, p_xts) ->
       fold (p_out::ps_out) (xts @ p_xts) ps ts
    | [], _::_ | _::_, [] ->
       assert false
  in
  fold [] [] ps ts


let rec infer_comp ({Location.thing=c; loc} : Dsyntax.comp) : (Rsyntax.comp * Mlty.ty) Tyenv.tyenvM =
  match c with

  | Dsyntax.Bound k ->
    Tyenv.lookup_bound k >>= fun t ->
    return (locate ~loc (Rsyntax.Bound k), t)

  | Dsyntax.Value pth ->
     Tyenv.lookup_ml_value pth >>= fun t ->
     return (locate ~loc (Rsyntax.Value pth), t)

  | Dsyntax.Function (x, annot, c) ->
     let a =
       begin
         match annot with
         | Dsyntax.Arg_annot_none -> Mlty.fresh_type ()
         | Dsyntax.Arg_annot_ty t -> ml_ty [] t
       end
     in
     Tyenv.add_bound_mono x a
     begin
       infer_comp c >>= fun (c, b) ->
       return (locate ~loc (Rsyntax.Function c), Mlty.Arrow (a, b))
     end

  | Dsyntax.Handler h ->
     handler ~loc h >>= fun (h, t) ->
     return (locate ~loc (Rsyntax.Handler h), t)

  | Dsyntax.TTConstructor (pth, cs) ->
    Tyenv.lookup_tt_constructor pth >>= fun c ->
    let rec fold cs_out = function
      | [] ->
        let cs_out = List.rev cs_out in
        let e = Rsyntax.TTConstructor (c, cs_out) in
        return (locate ~loc e, Mlty.Judgement)
      | c :: cs->
        check_comp c Mlty.Judgement >>= fun c ->
        fold (c :: cs_out) cs
    in
    fold [] cs

  | Dsyntax.MLConstructor (tag, cs) ->
    Tyenv.lookup_ml_constructor tag >>= fun (tag_id, ts, out) ->
    let tcs = List.combine ts cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        return (locate ~loc (Rsyntax.MLConstructor (tag_id, cs)), out)
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
        infer_comp c >>= fun (c, t) ->
        fold (c :: annot) (t :: ts) cs
    in
    fold [] [] cs

  | Dsyntax.Operation (op, cs) ->
    Tyenv.lookup_ml_operation op >>= fun (opid, (expected, out)) ->
    let tcs = List.combine expected cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        return (locate ~loc (Rsyntax.Operation (opid, cs)), out)
      | (t, c) :: tcs ->
        check_comp c t >>= fun c ->
        fold (c :: cs) tcs
    in
    fold [] tcs

  | Dsyntax.With (h, c) ->
    infer_comp h >>= fun (h, th) ->
    Tyenv.as_handler ~loc:h.Location.loc th >>= fun (a, b) ->
    check_comp c a >>= fun c ->
    return (locate ~loc (Rsyntax.With (h, c)), b)

  | Dsyntax.Let (clauses, c) ->
     let_clauses ~toplevel:false
       clauses (infer_comp c) >>= fun (_, clauses, (c, t)) ->
         return (locate ~loc (Rsyntax.Let (clauses, c)), t)

  | Dsyntax.LetRec (clauses, c) ->
     letrec_clauses ~toplevel:false
       clauses (infer_comp c) >>= fun (_, clauses, (c, t)) ->
         return (locate ~loc (Rsyntax.LetRec (clauses, c)), t)

  | Dsyntax.MLAscribe (c, sch) ->
      let sch = ml_schema sch in
      infer_comp c >>= fun (c, t) ->
       begin
         match generalizable c with
         | Generalizable ->
            Tyenv.generalizes_to ~loc:c.Location.loc t sch
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
     infer_comp x >>= fun (x, tx) ->
     Tyenv.as_dynamic ~loc:x.Location.loc tx >>= fun tx ->
     check_comp c1 tx >>= fun c1 ->
     infer_comp c2 >>= fun (c2, t) ->
     return (locate ~loc (Rsyntax.Now (x, c1, c2)), t)

  | Dsyntax.Current c ->
     infer_comp c >>= fun (c, t) ->
     Tyenv.as_dynamic ~loc:c.Location.loc t >>= fun t ->
     return (locate ~loc (Rsyntax.Current c), t)

  | Dsyntax.Lookup c ->
    infer_comp c >>= fun (c, t) ->
    Tyenv.as_ref ~loc:c.Location.loc t >>= fun t ->
    return (locate ~loc (Rsyntax.Lookup c), t)

  | Dsyntax.Update (c1, c2) ->
    infer_comp c1 >>= fun (c1, t1) ->
    Tyenv.as_ref ~loc:c1.Location.loc t1 >>= fun t ->
    check_comp c2 t >>= fun c2 ->
    return (locate ~loc (Rsyntax.Update (c1, c2)), Mlty.unit_ty)

  | Dsyntax.Ref c ->
    infer_comp c >>= fun (c, t) ->
    return (locate ~loc (Rsyntax.Ref c), Mlty.Ref t)

  | Dsyntax.Sequence (c1, c2) ->
    infer_comp c1 >>= fun (c1, _) ->
    (* TODO warn if not unit? *)
    infer_comp c2 >>= fun (c2, t) ->
    return (locate ~loc (Rsyntax.Sequence (c1, c2)), t)

  | Dsyntax.Assume ((None, c1), c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     infer_comp c2 >>= fun (c2, u) ->
     return (locate ~loc (Rsyntax.Assume ((None, c1), c2)), u)

  | Dsyntax.Assume ((Some x, c1), c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     Tyenv.add_bound_mono x Mlty.Judgement
     begin
       infer_comp c2 >>= fun (c2, u) ->
       return (locate ~loc (Rsyntax.Assume ((Some x, c1), c2)), u)
     end

  | Dsyntax.Match (c, cases) ->
    infer_comp c >>= fun (c, tc) ->
    match_cases ~loc tc cases >>= fun (cases, t) ->
    return (locate ~loc (Rsyntax.Match (c, cases)), t)

  | Dsyntax.BoundaryAscribe (c1, c2) ->
     check_comp c2 Mlty.Boundary >>= fun c2 ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     return (locate ~loc (Rsyntax.BoundaryAscribe (c1, c2)), Mlty.Judgement)

  | Dsyntax.TypeAscribe (c1, c2) ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     return (locate ~loc (Rsyntax.TypeAscribe (c1, c2)), Mlty.Judgement)

  | Dsyntax.Abstract (x, copt, c) ->
    begin match copt with
      | Some ct -> check_comp ct Mlty.Judgement >>= fun ct -> return (Some ct)
      | None -> return None
    end >>= fun copt ->
    Tyenv.add_bound_mono
      x
      Mlty.Judgement
      begin
        infer_comp c >>= fun (c,t) ->
        (* XXX verify whether we guarantee that [t] is normalized *)
        begin match t with
        | Mlty.Judgement ->
           let c = locate ~loc (Rsyntax.Abstract (x, copt, c)) in
           return (c, Mlty.Judgement)
        | Mlty.Boundary ->
           let c = locate ~loc (Rsyntax.Abstract (x, copt, c)) in
           return (c, Mlty.Boundary)
        | Mlty.Meta _ -> Mlty.error ~loc Mlty.UninferrableExpression
        | Mlty.(String | Param _ | Prod _ | Arrow _ | Handler _ | Apply _ | Ref _| Dynamic _) as t ->
           Mlty.error ~loc (Mlty.JudgementOrBoundaryExpected t)
        end
      end

  | Dsyntax.Substitute (c1, c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     return (locate ~loc (Rsyntax.Substitute (c1, c2)), Mlty.Judgement)

  | Dsyntax.Apply (c1, c2) ->
     infer_comp c1 >>= fun (c1, t1) ->
     infer_comp c2 >>= fun (c2, t2) ->
     let out = Mlty.fresh_type () in
     Tyenv.add_equation ~loc t1 (Mlty.Arrow (t2, out)) >>= fun () ->
     return (locate ~loc (Rsyntax.Apply (c1, c2)), out)

  | Dsyntax.Yield c ->
    Tyenv.lookup_continuation >>= fun (a, b) ->
    check_comp c a >>= fun c ->
    return (locate ~loc (Rsyntax.Yield c), b)

  | Dsyntax.String s -> return (locate ~loc (Rsyntax.String s), Mlty.String)

  | Dsyntax.Occurs (c1, c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     return (locate ~loc (Rsyntax.Occurs (c1, c2)), Mlty.Judgement)

  | Dsyntax.Convert (c1, c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     return (locate ~loc (Rsyntax.Convert (c1, c2)), Mlty.Judgement)

  | Dsyntax.Context c ->
     check_comp c Mlty.Judgement >>= fun c ->
     let t = Mlty.Apply (Desugar.Builtin.list, [Mlty.Judgement]) in
     return (locate ~loc (Rsyntax.Context c), t)

  | Dsyntax.Natural c ->
     check_comp c Mlty.Judgement >>= fun c ->
     return (locate ~loc (Rsyntax.Natural c), Mlty.Judgement)

  | Dsyntax.MLBoundary bdry ->
     boundary bdry >>= fun bdry ->
     return (locate ~loc Rsyntax.(MLBoundary bdry), Mlty.Boundary)

and check_comp c t =
  infer_comp c >>= fun (c, t') ->
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
      return (List.fold_left (fun acc (x, v) -> Ident.add x v acc) Ident.empty ops)
    | (op, cases) :: rem ->
      match_op_cases op cases output >>= fun op_cases ->
      fold (op_cases :: ops) rem
  in
  fold [] handler_ops >>= fun handler_ops ->
  return ({Rsyntax.handler_val=handler_val;handler_ops;handler_finally}, Mlty.Handler (input, final))

and match_case p t g c =
  check_pattern p t >>= fun (p, xts) ->
  Tyenv.add_bounds_mono xts
    (when_guard g >>= fun g ->
     infer_comp c >>= fun (c, tc) ->
     return (p, c, g, tc))

and when_guard =
  let mlbool = Mlty.Apply (Desugar.Builtin.bool, []) in
  function
  | None -> return None
  | Some c ->
     check_comp c mlbool >>= fun c ->
     return (Some c)

and check_match_case p tp g c tc =
  check_pattern p tp >>= fun (p, xts) ->
  Tyenv.add_bounds_mono xts
    (when_guard g >>= fun g ->
     check_comp c tc >>= fun c ->
     return (p, g, c))

and match_cases ~loc t = function
  | [] ->
     return ([], Mlty.fresh_type ())

  | (p1, g1, c1) :: cases ->
     match_case p1 t g1 c1 >>= fun (p1, c1, g1, out) ->
     let rec fold cases = function
       | [] ->
          let cases = List.rev cases in
          return (cases, out)
       | (p, g, c) :: others ->
          check_match_case p t g c out >>= fun (p, g, c) ->
          fold ((p, g, c) :: cases) others
      in
      fold [(p1, g1, c1)] cases

and match_op_cases op cases t_out =
  Tyenv.op_cases
    op ~output:t_out
    (fun oid ts ->
      let rec fold_cases cases = function
        | [] -> return (oid, List.rev cases)
        | (ps, popt, c) :: rem ->
           let rec fold_args ps_out xts ps ts =
             match ps, ts with

             | [], [] ->
                let ps_out = List.rev ps_out in
                begin match popt with
                | None -> return (None, xts)
                | Some p ->
                   check_boundary_pattern p >>= fun (p, xts_p) ->
                   return (Some p, xts @ xts_p)
                end >>= fun (popt, xts) ->
                Tyenv.add_bounds_mono xts
                  (check_comp c t_out >>= fun c ->
                   return (ps_out, popt, c))

             | p::ps, t::ts ->
                check_pattern p t >>= fun (p, xts_p) ->
                fold_args (p :: ps_out) (xts @ xts_p) ps ts

             | [], _::_ | _::_, [] ->
                assert false
           in
           fold_args [] [] ps ts >>= fun case ->
           fold_cases (case :: cases) rem
      in
      fold_cases [] cases)


and let_clauses
  : 'a . toplevel:bool -> Dsyntax.let_clause list -> 'a Tyenv.tyenvM ->
         ((Name.t * Mlty.ty_schema) list list * Rsyntax.let_clause list * 'a) Tyenv.tyenvM
  = fun ~toplevel clauses_in m ->
  let rec fold_rhs cts = function
    | [] -> return (List.rev cts)
    | Dsyntax.Let_clause (p, annot, c) :: clauses_in ->
       infer_comp c >>= fun (c, t) ->
       fold_rhs ((p, annot, c, t) :: cts) clauses_in
  in

  let rec fold_lhs clauses_out = function
    | [] -> return (List.rev clauses_out)

    | (p, annot, c, t) :: clauses_in ->
       check_pattern p t >>= fun (p, xts) ->
       begin match generalizable c with

       | Generalizable ->
          begin match annot with
          | Dsyntax.Let_annot_schema sch ->
             let sch = ml_schema sch in
             Tyenv.generalizes_to ~loc:c.Location.loc t sch

          | Dsyntax.Let_annot_none -> return ()
          end >>= fun () ->

          let rec fold xss = function
            | [] -> fold_lhs ((List.rev xss, p, c) :: clauses_out) clauses_in
            | (x,t) :: xts ->
               Tyenv.generalize t >>= fun sch ->
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
            | [] -> fold_lhs ((List.rev xss, p, c) :: clauses_out) clauses_in
            | (x,t) :: xts ->
               Tyenv.ungeneralize t >>= fun sch ->
               fold ((x,sch) :: xss) xts
          in
          fold [] xts
       end
  in
  fold_rhs [] clauses_in >>= fun pacts ->
  fold_lhs [] pacts >>= fun clauses ->
  let rec fold info_out clauses_out = function
    | [] ->
       let clauses_out = List.rev clauses_out in
       let info_out = List.rev info_out in
       m >>= fun r -> return (info_out, clauses_out, r)
    | (xss, p, c) :: clauses_in ->
       (if toplevel then Tyenv.add_ml_values_poly else Tyenv.add_bounds_poly) xss
         (fold (xss :: info_out) ((Rsyntax.Let_clause (p, c)) :: clauses_out) clauses_in)
  in
  fold [] [] clauses

and letrec_clauses
  :  'a . toplevel:bool -> Dsyntax.letrec_clause list ->
          'a Tyenv.tyenvM -> ((Name.t * Mlty.ty_schema) list * Rsyntax.letrec_clause list * 'a) Tyenv.tyenvM
  = fun ~toplevel fycs m ->

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
       (if toplevel then Tyenv.add_ml_value_poly else Tyenv.add_bound_poly)
         f sch
         (bind_functions ((f, schopt, y, a, c, b) :: acc) rem)
  in

  let rec check_bodies acc = function
    | [] -> return (List.rev acc)

    | (f, schopt, y, a, c, b) :: rem ->
       Tyenv.add_bound_mono y a (check_comp c b) >>= fun c ->
       check_bodies ((f, schopt, y, a, c, b) :: acc) rem
  in

  let rec generalize_funs info clauses = function
    | [] -> return (List.rev info, List.rev clauses)

    | (f, Some sch, y, a, c, b) :: rem ->
       let t = Mlty.Arrow (a, b) in
       Tyenv.generalizes_to ~loc:c.Location.loc t sch >>= fun () ->
       generalize_funs ((f, sch) :: info) (Rsyntax.Letrec_clause c :: clauses) rem

    | (f, None, y, a, c, b) :: rem ->
       let t = Mlty.Arrow (a, b) in
       Tyenv.generalize t >>= fun sch ->
       generalize_funs ((f, sch) :: info) (Rsyntax.Letrec_clause c :: clauses) rem

  in

  bind_functions [] fycs >>=
  check_bodies []  >>=
  generalize_funs [] [] >>= fun (info, clauses) ->
  m >>= fun x ->
  return (info, clauses, x)

and boundary = function
  | Dsyntax.BoundaryIsType ->
     return Rsyntax.BoundaryIsType

  | Dsyntax.BoundaryIsTerm c ->
     check_comp c Mlty.Judgement >>= fun c ->
     return (Rsyntax.BoundaryIsTerm c)

  | Dsyntax.BoundaryEqType (c1, c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     return (Rsyntax.BoundaryEqType (c1, c2))

  | Dsyntax.BoundaryEqTerm (c1, c2, c3) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     check_comp c3 Mlty.Judgement >>= fun c3 ->
     return (Rsyntax.BoundaryEqTerm (c1, c2, c3))

let add_ml_type (t, (params, def)) =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  match def with

    | Dsyntax.ML_Alias t' ->
       let t' = ml_ty params t' in
       Tyenv.add_ml_type t (Mlty.Alias (params, t'))

    | Dsyntax.ML_Sum constructors ->
       let mk_path name k =
         match t with
         | Path.Direct _ -> Path.Direct (Path.Level (name, k))
         | Path.Module (mdl, _) -> Path.Module (mdl, Path.Level (name, k))
       in
       let rec fold k acc = function
         | [] -> List.rev acc
         | (name, ts) :: lst ->
            let tag_id = Ident.create (mk_path name k) in
            let acc = (tag_id, List.map (ml_ty params) ts) :: acc in
            fold (k+1) acc lst
       in
       let constructors = fold 0 [] constructors in
       Tyenv.add_ml_type t (Mlty.Sum (params, constructors))

let local_context lctx m =
  let rec fold xcs = function
    | [] ->
       let xcs = List.rev xcs in
       m >>= fun x -> return (xcs, x)
    | (x, c) :: lctx ->
       check_comp c Mlty.Judgement >>= fun c ->
       Tyenv.add_bound_mono x Mlty.Judgement
       (fold ((x, c) :: xcs) lctx)
  in
  fold [] lctx

let premise {Location.thing=prem;loc} =
  let Dsyntax.Premise (x, lctx, bdry) = prem in
  local_context lctx (boundary bdry) >>= fun (lctx, bdry) ->
  let p = locate ~loc (Rsyntax.Premise (x, lctx, bdry)) in
  return (x, p)

let premises prems m =
  let rec fold ps = function
    | [] ->
       m >>= fun x ->
       let ps = List.rev ps in return (ps, x)
    | prem :: prems ->
       premise prem >>= fun (x, p) ->
       Tyenv.add_bound_mono x Mlty.Judgement (fold (p::ps) prems)
  in
  fold [] prems

let boundary = function
  | Dsyntax.BoundaryIsType ->
     return Rsyntax.BoundaryIsType

  | Dsyntax.BoundaryIsTerm c ->
     check_comp c Mlty.Judgement >>= fun c ->
     return (Rsyntax.BoundaryIsTerm c)

  | Dsyntax.BoundaryEqType (c1, c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     return (Rsyntax.BoundaryEqType (c1, c2))

  | Dsyntax.BoundaryEqTerm (c1, c2, c3) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     check_comp c3 Mlty.Judgement >>= fun c3 ->
     return (Rsyntax.BoundaryEqTerm (c1, c2, c3))

let rec toplevel' ({Location.thing=c; loc} : Dsyntax.toplevel) =
  match c with

  | Dsyntax.Rule (rname, prems, bdry) ->
     premises prems (boundary bdry) >>= fun (ps, bdry) ->
     let r = Ident.create rname in
     Tyenv.add_tt_constructor r >>= fun () ->
     return_located ~loc (Rsyntax.Rule (r, ps, bdry))

  (* Desugar is the only place where recursion/nonrecursion matters,
     so [DefMLType] and [DefMLTypeRec] behave the same way in typechecking. *)
  | Dsyntax.DefMLType tydefs ->
     let rec fold = function
       | [] -> return_located ~loc (Rsyntax.DefMLType (List.map fst tydefs))
       | tydef :: tydefs ->
          add_ml_type tydef >>= fun () -> fold tydefs
     in
     fold tydefs

  | Dsyntax.DefMLTypeRec tydefs ->
     let rec fold = function
       | [] -> return_located ~loc (Rsyntax.DefMLTypeRec (List.map fst tydefs))
       | tydef :: tydefs -> add_ml_type tydef >>= fun () -> fold tydefs
     in
     fold tydefs

  | Dsyntax.DeclOperation (op, (tys_in, ty_out)) ->
    let tys_in = List.map (ml_ty []) tys_in in
    let ty_out = ml_ty [] ty_out in
    Tyenv.add_ml_operation op (tys_in, ty_out) >>= fun () ->
    return_located ~loc (Rsyntax.DeclOperation (op, (tys_in, ty_out)))

  | Dsyntax.DeclExternal (x, sch, s) ->
     let sch = ml_schema sch in
     Tyenv.add_ml_value_poly x sch
        (return_located ~loc (Rsyntax.DeclExternal (x, sch, s)))

  | Dsyntax.TopLet clauses ->
     let_clauses ~toplevel:true clauses (return ()) >>= fun (info, clauses, ()) ->
     return_located ~loc (Rsyntax.TopLet (info, clauses))

  | Dsyntax.TopLetRec clauses ->
     letrec_clauses ~toplevel:true clauses (return ()) >>= fun (info, clauses, ()) ->
     return_located ~loc (Rsyntax.TopLetRec (info, clauses))

  | Dsyntax.TopComputation c ->
     infer_comp c >>= fun (c, t) ->
     begin
       match generalizable c with
       | Generalizable ->
          Tyenv.generalize t >>= fun sch ->
          return_located ~loc (Rsyntax.TopComputation (c, sch))
       |  Ungeneralizable ->
          Tyenv.ungeneralize t >>= fun sch ->
          return_located ~loc (Rsyntax.TopComputation (c, sch))
     end

  | Dsyntax.TopDynamic (x, annot, c) ->
     infer_comp c >>= fun (c, t) ->
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
     Tyenv.add_ml_value_poly x sch
       (return_located ~loc (Rsyntax.TopDynamic (x, sch, c)))

  | Dsyntax.TopNow (x, c) ->
       infer_comp x >>= fun (x, tx) ->
       Tyenv.as_dynamic ~loc:x.Location.loc tx >>= fun tx ->
       check_comp c tx >>= fun c ->
       return_located ~loc (Rsyntax.TopNow (x, c))

  | Dsyntax.Verbosity v ->
    return_located ~loc (Rsyntax.Verbosity v)

  | Dsyntax.Open pth ->
     return_located ~loc (Rsyntax.Open pth)

  | Dsyntax.MLModule (mdl_name, cs) ->
     Tyenv.as_module (toplevels' cs) >>= fun cs ->
     return_located ~loc (Rsyntax.MLModule (mdl_name, cs))

and toplevels' cs =
  let rec fold cs_out = function
    | [] -> return (List.rev cs_out)
    | c :: cs ->
       toplevel' c >>= fun c ->
       fold (c :: cs_out) cs
  in
  fold [] cs

(** The publicly available version of [toplvel'] *)
let toplevel env c = Tyenv.run env (toplevel' c)

(** The publicly available version of [toplevels'] *)
let toplevels env cs = Tyenv.run env (toplevels' cs)

let initial_context, initial_commands =
  let ctx, cmds =
    List.fold_left
      (fun (typing, cmds) cmd ->
        let typing, cmd = toplevel typing cmd in
        (typing, cmd :: cmds))
      (Tyenv.empty, [])
      Desugar.initial_commands
  in
  let cmds = List.rev cmds in
  ctx, cmds

module Builtin =
struct
  let run m = Tyenv.run initial_context m

  let _, nil = run (Tyenv.lookup_ml_constructor Desugar.Builtin.nil)
  let _, cons = run (Tyenv.lookup_ml_constructor Desugar.Builtin.cons)

  let _, none = run (Tyenv.lookup_ml_constructor Desugar.Builtin.none)
  let _, some = run (Tyenv.lookup_ml_constructor Desugar.Builtin.some)

  let _, mlless = run (Tyenv.lookup_ml_constructor Desugar.Builtin.mlless)
  let _, mlequal = run (Tyenv.lookup_ml_constructor Desugar.Builtin.mlequal)
  let _, mlgreater = run (Tyenv.lookup_ml_constructor Desugar.Builtin.mlgreater)

  let _, mlfalse = run (Tyenv.lookup_ml_constructor Desugar.Builtin.mlfalse)
  let _, mltrue = run (Tyenv.lookup_ml_constructor Desugar.Builtin.mltrue)

  (* the [Tyenv] monad is annoying as hell, let's get rid of ste stupid monads as much as we can,
     they are not idiomatic in OCaml *)
  let _, equal_term = run (Tyenv.lookup_ml_operation Desugar.Builtin.equal_term)

  let _, equal_type = run (Tyenv.lookup_ml_operation Desugar.Builtin.equal_type)

  let _, coerce = run (Tyenv.lookup_ml_operation Desugar.Builtin.coerce)
end
