(** Bidirectional Hindley-Milner typechecking. *)

let (>>=) = Tyenv.(>>=)
let return = Tyenv.return

let locate ~at v = Location.mark ~at v

let return_located ~at v = return (Location.mark ~at v)

(** Is a computation generalizable *)
type generalizable =
  | Generalizable
  | Ungeneralizable

let rec generalizable c =
  match c.Location.it with
  (* yes *)
  | Syntax.(Bound _ | Value _ | Function _ | Handler _| String _ | Raise _) ->
     Generalizable

  | Syntax.MLConstructor (_, cs) | Syntax.Tuple cs ->
     if List.for_all (fun c -> generalizable c = Generalizable) cs
     then
       Generalizable
     else
       Ungeneralizable

  | Syntax.Let (_, c)
  | Syntax.LetRec (_, c)
  | Syntax.Sequence (_, c) -> generalizable c

  (* no *)
  | Syntax.(
      Operation _
    | MLException _
    | With _
    | Lookup _
    | Update _
    | Ref _
    | Fresh _
    | AbstractAtom _
    | Match _
    | BoundaryAscribe _
    | TypeAscribe _
    | TTConstructor _
    | TTApply _
    | Abstract _
    | SubstituteJudgement _
    | SubstituteBoundary _
    | Derive _
    | Apply _
    | Occurs _
    | Congruence _
    | Convert _
    | Context _
    | Natural _
    | MLBoundary _)
  -> Ungeneralizable

(* Instantite the bound parameters in a type with the given ones. *)
let rec ml_ty params {Location.it=t; at} =
  match t with

  | Desugared.ML_Arrow (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Mlty.Arrow (t1, t2)

  | Desugared.ML_Prod ts ->
    let ts = List.map (ml_ty params) ts in
    Mlty.Prod ts

  | Desugared.ML_Apply (pth, ts) ->
    let ts = List.map (ml_ty params) ts in
    Mlty.Apply (pth, ts)

  | Desugared.ML_Handler (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Mlty.Handler (t1, t2)

  | Desugared.ML_Ref t ->
     let t = ml_ty params t in
     Mlty.Ref t

  | Desugared.ML_Exn ->
     Mlty.Exn

  | Desugared.ML_Judgement ->
     Mlty.Judgement

  | Desugared.ML_Derivation ->
     Mlty.Derivation

  | Desugared.ML_Boundary ->
     Mlty.Boundary

  | Desugared.ML_String ->
     Mlty.String

  | Desugared.ML_Bound (Path.Index (_, i)) ->
     Mlty.Param (List.nth params i)

  | Desugared.ML_Anonymous ->
     Mlty.fresh_type ()

(* Return a fresh instance of the given schema, with a list of freshly generated parameters. *)
let ml_schema {Location.it=(Desugared.ML_Forall (params, t)); _} =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  let t = ml_ty params t in
  (params, t)

(** Infer the type of a pattern *)
let rec infer_pattern {Location.it=p; at} =
  match p with
  | Desugared.Patt_Anonymous ->
     return (locate ~at Syntax.Patt_Anonymous, Mlty.fresh_type (), [])

  | Desugared.Patt_Var x ->
     let t = Mlty.fresh_type () in
     return (locate ~at Syntax.Patt_Var, t, [(x, t)])

  | Desugared.Patt_MLAscribe (p, t) ->
     let t = ml_ty [] t in
     check_pattern p t >>= fun (p, xts) ->
     return (p, t, xts)

  | Desugared.Patt_As (p1, p2) ->
     infer_pattern p1 >>= fun (p1, t1, xts1) ->
     check_pattern p2 t1 >>= fun (p2, xts2) ->
     return (locate ~at (Syntax.Patt_As (p1, p2)), t1, xts1 @ xts2)

  | Desugared.Patt_MLConstructor (tag, ps) ->
    Tyenv.lookup_ml_constructor tag >>= fun (tag_id, ts, out) ->
    check_patterns ps ts >>= fun (ps, xts) ->
    return (locate ~at (Syntax.Patt_MLConstructor (tag_id, ps)), out, xts)

  | Desugared.Patt_MLException (exc, popt) ->
    Tyenv.lookup_ml_exception exc >>= fun (exc, topt) ->
    begin match popt, topt with
    | None, None -> return (locate ~at (Syntax.Patt_MLException (exc, None)), Mlty.Exn, [])
    | Some p, Some t ->
       check_pattern p t >>= fun (p, xts) ->
       return (locate ~at (Syntax.Patt_MLException (exc, Some p)), Mlty.Exn, xts)
    | Some _, None | None, Some _ -> assert false (* prevented by desugaring *)
    end

  | Desugared.Patt_TTConstructor (c, ps) ->
     Tyenv.lookup_tt_constructor c >>= fun c ->
     let ts = List.map (fun _ -> Mlty.Judgement) ps in
     check_patterns ps ts >>= fun (ps, xts) ->
     return (locate ~at (Syntax.Patt_TTConstructor (c, ps)), Mlty.Judgement, xts)

  | Desugared.Patt_GenAtom p ->
     check_pattern p Mlty.Judgement >>= fun (p, xts) ->
     return (locate ~at (Syntax.Patt_GenAtom p), Mlty.Judgement, xts)

  | Desugared.Patt_IsType p ->
     check_pattern p Mlty.Judgement >>= fun (p, xts) ->
     return (locate ~at (Syntax.Patt_IsType p), Mlty.Judgement, xts)

  | Desugared.Patt_IsTerm (p1, p2) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     return (locate ~at (Syntax.Patt_IsTerm (p1, p2)), Mlty.Judgement, xts1 @ xts2)

  | Desugared.Patt_EqType (p1, p2) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     return (locate ~at (Syntax.Patt_EqType (p1, p2)), Mlty.Judgement, xts1 @ xts2)

  | Desugared.Patt_EqTerm (p1, p2, p3) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     check_pattern p3 Mlty.Judgement >>= fun (p3, xts3) ->
     return (locate ~at (Syntax.Patt_EqTerm (p1, p2, p3)), Mlty.Judgement, xts1 @ xts2 @ xts3)

  | Desugared.Patt_BoundaryIsType ->
     return (locate ~at (Syntax.Patt_BoundaryIsType), Mlty.Boundary, [])

  | Desugared.Patt_BoundaryIsTerm p ->
     check_pattern p Mlty.Judgement >>= fun (p, xts) ->
     return (locate ~at (Syntax.Patt_BoundaryIsTerm p), Mlty.Boundary, xts)

  | Desugared.Patt_BoundaryEqType (p1, p2) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     return (locate ~at (Syntax.Patt_BoundaryEqType (p1, p2)), Mlty.Boundary, xts1 @ xts2)

  | Desugared.Patt_BoundaryEqTerm (p1, p2, p3) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     check_pattern p2 Mlty.Judgement >>= fun (p2, xts2) ->
     check_pattern p3 Mlty.Judgement >>= fun (p3, xts3) ->
     return (locate ~at (Syntax.Patt_BoundaryEqTerm (p1, p2, p3)), Mlty.Boundary, xts1 @ xts2 @ xts3)

  | Desugared.Patt_Abstraction (xopt, p1, p2) ->
     check_pattern p1 Mlty.Judgement >>= fun (p1, xts1) ->
     infer_pattern p2 >>= fun (p2, t2, xts2) ->
     let xts2 =
       match xopt with
       | None -> xts2
       | Some x -> (x, Mlty.Judgement) :: xts2
     in
     Tyenv.as_judgement_or_boundary ~at t2 >>=
       begin function
         | Tyenv.Is_judgement ->
            return (locate ~at (Syntax.Patt_Abstract (xopt, p1, p2)), Mlty.Judgement, xts1 @ xts2)
         | Tyenv.Is_boundary ->
            return (locate ~at (Syntax.Patt_Abstract (xopt, p1, p2)), Mlty.Boundary, xts1 @ xts2)
       end

  | Desugared.Patt_Tuple ps ->
    let rec fold qs ts xts = function
      | [] ->
         let qs = List.rev qs
         and ts = List.rev ts in
         return (locate ~at (Syntax.Patt_Tuple qs), Mlty.Prod ts, xts)
      | p :: ps ->
         infer_pattern p >>= fun (q, t, p_xts) ->
         fold (q :: qs) (t :: ts) (xts @ p_xts) ps
    in
    fold [] [] [] ps

  | Desugared.Patt_String s ->
     return (locate ~at (Syntax.Patt_String s), Mlty.String, [])

and check_pattern ({Location.it=p'; at} as p) t =
  match p' with
  | Desugared.Patt_Anonymous ->
     return (locate ~at Syntax.Patt_Anonymous, [])

  | Desugared.Patt_Var x ->
     return (locate ~at Syntax.Patt_Var, [(x, t)])

  | Desugared.Patt_MLAscribe (p, t') ->
     let t' = ml_ty [] t' in
     check_pattern p t' >>= fun (p, xts) ->
     Tyenv.add_equation ~at t' t >>= fun () ->
     return (p, xts)

  | Desugared.Patt_As (p1, p2) ->
     check_pattern p1 t >>= fun (p1, xts1) ->
     check_pattern p2 t >>= fun (p2, xts2) ->
     return (locate ~at (Syntax.Patt_As (p1, p2)), xts1 @ xts2)

  | Desugared.Patt_Tuple ps ->
     begin match t with
     | Mlty.Prod ts when (List.length ps = List.length ts) ->
        check_patterns ps ts >>= fun (ps, xts) ->
        return (locate ~at (Syntax.Patt_Tuple ps), xts)

     | Mlty.(Prod _ | Judgement | Boundary | Derivation | String | Meta _ | Param _ |
             Arrow _ | Handler _ | Apply _ | Ref _ | Exn) ->
        infer_pattern p >>= fun (p, t', xts) ->
        Tyenv.add_equation ~at t' t >>= fun () ->
        return (p, xts)
     end

  | Desugared.(Patt_MLException _ | Patt_MLConstructor _ | Patt_TTConstructor _ | Patt_String _ |
             Patt_BoundaryIsType | Patt_BoundaryIsTerm _ | Patt_BoundaryEqType _ | Patt_BoundaryEqTerm _ |
             Patt_GenAtom _ | Patt_IsType _ | Patt_IsTerm _ | Patt_EqType _ | Patt_EqTerm _ | Patt_Abstraction _)->
     infer_pattern p >>= fun (p, t', xts) ->
     Tyenv.add_equation ~at:p.Location.at t' t >>= fun () ->
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


let rec infer_comp ({Location.it=c; at} : Desugared.comp) : (Syntax.comp * Mlty.ty) Tyenv.tyenvM =
  match c with

  | Desugared.Bound k ->
    Tyenv.lookup_bound k >>= fun t ->
    return (locate ~at (Syntax.Bound k), t)

  | Desugared.Value pth ->
     Tyenv.lookup_ml_value pth >>= fun t ->
     return (locate ~at (Syntax.Value pth), t)

  | Desugared.Function (x, annot, c) ->
     let a =
       begin
         match annot with
         | Desugared.Arg_annot_none -> Mlty.fresh_type ()
         | Desugared.Arg_annot_ty t -> ml_ty [] t
       end
     in
     Tyenv.add_bound_mono x a
     begin
       infer_comp c >>= fun (c, b) ->
       return (locate ~at (Syntax.Function c), Mlty.Arrow (a, b))
     end

  | Desugared.Handler h ->
     infer_handler ~at h >>= fun (h, t) ->
     return (locate ~at (Syntax.Handler h), t)

  | Desugared.TTConstructor (pth, cs) ->
    Tyenv.lookup_tt_constructor pth >>= fun c ->
    let rec fold cs_out = function
      | [] ->
        let cs_out = List.rev cs_out in
        let e = Syntax.TTConstructor (c, cs_out) in
        return (locate ~at e, Mlty.Judgement)
      | c :: cs->
        check_comp c Mlty.Judgement >>= fun c ->
        fold (c :: cs_out) cs
    in
    fold [] cs

  | Desugared.MLConstructor (tag, cs) ->
    Tyenv.lookup_ml_constructor tag >>= fun (tag_id, ts, out) ->
    let tcs = List.combine ts cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        return (locate ~at (Syntax.MLConstructor (tag_id, cs)), out)
      | (t, c) :: tcs ->
        check_comp c t >>= fun c ->
        fold (c :: cs) tcs
    in
    fold [] tcs

  | Desugared.MLException (exc, copt) ->
     Tyenv.lookup_ml_exception exc >>= fun (exc_id, topt) ->
       begin match copt, topt with
       | None, None ->
          return (locate ~at (Syntax.MLException (exc_id, None)), Mlty.Exn)
       | Some c, Some t ->
          check_comp c t >>= fun c ->
          return (locate ~at (Syntax.MLException (exc_id, Some c)), Mlty.Exn)
       | None, Some _ | Some _, None ->
          assert false (* desugaring took care of this *)
       end

  | Desugared.Tuple cs ->
    let rec fold annot ts = function
      | [] ->
        let ts = List.rev ts
        and cs = List.rev annot in
        return (locate ~at (Syntax.Tuple cs), Mlty.Prod ts)
      | c :: cs ->
        infer_comp c >>= fun (c, t) ->
        fold (c :: annot) (t :: ts) cs
    in
    fold [] [] cs

  | Desugared.Operation (op, cs) ->
    Tyenv.lookup_ml_operation op >>= fun (opid, (expected, out)) ->
    let tcs = List.combine expected cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        return (locate ~at (Syntax.Operation (opid, cs)), out)
      | (t, c) :: tcs ->
        check_comp c t >>= fun c ->
        fold (c :: cs) tcs
    in
    fold [] tcs

  | Desugared.Raise c ->
     check_comp c Mlty.Exn >>= fun c ->
     let t = Mlty.fresh_type () in
     return (locate ~at (Syntax.Raise c), t)

  | Desugared.With (h, c) ->
    infer_comp h >>= fun (h, th) ->
    Tyenv.as_handler ~at:h.Location.at th >>= fun (a, b) ->
    check_comp c a >>= fun c ->
    return (locate ~at (Syntax.With (h, c)), b)

  | Desugared.Let (clauses, c) ->
     let_clauses ~toplevel:false
       clauses (infer_comp c) >>= fun (_, clauses, (c, t)) ->
         return (locate ~at (Syntax.Let (clauses, c)), t)

  | Desugared.LetRec (clauses, c) ->
     letrec_clauses ~toplevel:false
       clauses (infer_comp c) >>= fun (_, clauses, (c, t)) ->
         return (locate ~at (Syntax.LetRec (clauses, c)), t)

  | Desugared.MLAscribe (c, sch) ->
      let sch = ml_schema sch in
      infer_comp c >>= fun (c, t) ->
       begin
         match generalizable c with
         | Generalizable ->
            Tyenv.generalizes_to ~at:c.Location.at t sch
         | Ungeneralizable ->
            begin
              match sch with
              | ([], tsch) ->
                 Tyenv.add_equation ~at:c.Location.at t tsch
              | (_::_, _) ->
                 Mlty.error ~at:c.Location.at Mlty.ValueRestriction
            end
       end >>= fun () -> return (c, t)

  | Desugared.Lookup c ->
    infer_comp c >>= fun (c, t) ->
    Tyenv.as_ref ~at:c.Location.at t >>= fun t ->
    return (locate ~at (Syntax.Lookup c), t)

  | Desugared.Update (c1, c2) ->
    infer_comp c1 >>= fun (c1, t1) ->
    Tyenv.as_ref ~at:c1.Location.at t1 >>= fun t ->
    check_comp c2 t >>= fun c2 ->
    return (locate ~at (Syntax.Update (c1, c2)), Mlty.unit_ty)

  | Desugared.Ref c ->
    infer_comp c >>= fun (c, t) ->
    return (locate ~at (Syntax.Ref c), Mlty.Ref t)

  | Desugared.Sequence (c1, c2) ->
    infer_comp c1 >>= fun (c1, _) ->
    (* TODO warn if not unit? *)
    infer_comp c2 >>= fun (c2, t) ->
    return (locate ~at (Syntax.Sequence (c1, c2)), t)

  | Desugared.Fresh (xopt, c) ->
     check_comp c Mlty.Judgement >>= fun c ->
     return (locate ~at (Syntax.Fresh (xopt, c)), Mlty.Judgement)

   | Desugared.AbstractAtom (c1, c2) ->
      check_comp c1 Mlty.Judgement >>= fun c1 ->
      begin
      infer_comp c2 >>= fun (c2,t) ->
        Tyenv.as_judgement_or_boundary ~at t >>=
          begin function
            | Tyenv.Is_judgement ->
               let c = locate ~at (Syntax.AbstractAtom (c1, c2)) in
               return (c, Mlty.Judgement)
            | Tyenv.Is_boundary ->
               let c = locate ~at (Syntax.AbstractAtom (c1, c2)) in
               return (c, Mlty.Boundary)
      end
   end

  | Desugared.Match (c, cases) ->
    infer_comp c >>= fun (c, tc) ->
    match_cases ~at tc cases >>= fun (cases, t) ->
    return (locate ~at (Syntax.Match (c, cases)), t)

  | Desugared.BoundaryAscribe (c1, c2) ->
     check_comp c2 Mlty.Boundary >>= fun c2 ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     return (locate ~at (Syntax.BoundaryAscribe (c1, c2)), Mlty.Judgement)

  | Desugared.TypeAscribe (c1, c2) ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     return (locate ~at (Syntax.TypeAscribe (c1, c2)), Mlty.Judgement)

  | Desugared.Abstract (x, copt, c) ->
    begin match copt with
      | Some ct -> check_comp ct Mlty.Judgement >>= fun ct -> return (Some ct)
      | None -> return None
    end >>= fun copt ->
    Tyenv.add_bound_mono
      x
      Mlty.Judgement
      begin
        infer_comp c >>= fun (c,t) ->
        Tyenv.as_judgement_or_boundary ~at t >>=
          begin function
            | Tyenv.Is_judgement ->
               let c = locate ~at (Syntax.Abstract (x, copt, c)) in
               return (c, Mlty.Judgement)
            | Tyenv.Is_boundary ->
               let c = locate ~at (Syntax.Abstract (x, copt, c)) in
               return (c, Mlty.Boundary)
        end
      end

  | Desugared.Substitute (c1, c2) ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     infer_comp c1 >>= fun (c1,t1) ->
     Tyenv.as_judgement_or_boundary ~at t1 >>=
       begin function
         | Tyenv.Is_judgement -> return (locate ~at (Syntax.SubstituteJudgement (c1, c2)), Mlty.Judgement)
         | Tyenv.Is_boundary -> return (locate ~at (Syntax.SubstituteBoundary (c1, c2)), Mlty.Boundary)
       end

  | Desugared.Derive (ps, c) ->
     premises ps (check_comp c Mlty.Judgement) >>= fun (ps, c) ->
     return (locate ~at (Syntax.Derive (ps, c)), Mlty.Derivation)

  | Desugared.Spine (c, cs) ->
     infer_spine ~at c cs

  | Desugared.String s -> return (locate ~at (Syntax.String s), Mlty.String)

  | Desugared.Occurs (c1, c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     return (locate ~at (Syntax.Occurs (c1, c2)), Mlty.Judgement)

  | Desugared.Congruence (c1, c2, cs) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     let rec fold cs_out = function
       | [] ->
          let cs_out = List.rev cs_out in
          return (locate ~at (Syntax.Congruence (c1, c2, cs_out)), Mlty.Judgement)
       | c :: cs ->
          check_comp c Mlty.Judgement >>= fun c ->
          fold (c :: cs_out) cs
     in
     fold [] cs

  | Desugared.Convert (c1, c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     return (locate ~at (Syntax.Convert (c1, c2)), Mlty.Judgement)

  | Desugared.Context c ->
     check_comp c Mlty.Judgement >>= fun c ->
     let t = Mlty.Apply (Desugar.Builtin.list, [Mlty.Judgement]) in
     return (locate ~at (Syntax.Context c), t)

  | Desugared.Natural c ->
     check_comp c Mlty.Judgement >>= fun c ->
     return (locate ~at (Syntax.Natural c), Mlty.Judgement)

  | Desugared.MLBoundary bdry ->
     boundary bdry >>= fun bdry ->
     return (locate ~at Syntax.(MLBoundary bdry), Mlty.Boundary)

and infer_spine ~at c_head cs =
  let rec fold t_head c_head cs =
    Tyenv.as_derivation_or_function ~at t_head >>= function

    | Tyenv.Is_derivation ->
       (** It's a derivation *)
       let rec fold cs_out = function
         | [] ->
            let cs_out = List.rev cs_out in
            return (locate ~at Syntax.(TTApply (c_head, cs_out)), Mlty.Judgement)
         | c :: cs ->
            check_comp c Mlty.Judgement >>= fun c_out ->
            fold (c_out :: cs_out) cs
       in
       fold [] cs

    | Tyenv.Is_function (u, v) ->
       (** It's an ML application *)
       begin match cs with
       | [] -> assert false
       | [c] ->
          check_comp c u >>= fun c ->
          return (locate ~at (Syntax.Apply (c_head, c)), v)
       | c :: cs ->
          check_comp c u >>= fun c ->
          let c_head = locate ~at (Syntax.Apply (c_head, c)) in
          fold v c_head cs
       end
  in
  infer_comp c_head >>= fun (c_head, t_head) ->
  fold t_head c_head cs

and infer_handler ~at Desugared.{handler_val=handler_val;handler_ops;handler_exc} =
  let input = Mlty.fresh_type () in
  (* value case *)
  begin match handler_val with
    | [] -> return ([], input)
    | _ :: _ -> match_cases ~at input handler_val
  end >>=
  (* handler cases *)
  fun (handler_val, output) ->
  check_match_cases ~at Mlty.Exn output handler_exc >>=
  fun handler_exc ->
  (* operation cases *)
  let rec fold ops = function
    | [] ->
      return (List.fold_left (fun acc (x, v) -> Ident.add x v acc) Ident.empty ops)
    | (op, cases) :: rem ->
      match_op_cases op cases >>= fun op_cases ->
      fold (op_cases :: ops) rem
  in
  fold [] handler_ops >>= fun handler_ops ->
  return (Syntax.{handler_val; handler_ops; handler_exc}, Mlty.Handler (input, output))

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

and check_match_cases ~at tp tc cases =
  let rec fold cases' = function
  | [] ->
     let cases' = List.rev cases' in
     return cases'

  | (p, g, c) :: cases ->
     check_match_case p tp g c tc >>= fun (p, g, c) ->
     fold ((p, g, c) :: cases') cases
  in
  fold [] cases

and match_cases ~at t = function
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

and match_op_cases op cases =
  Tyenv.lookup_ml_operation op >>= fun (oid, (ts, t_out)) ->
  let rec fold_cases cases' = function
    | [] -> return (oid, List.rev cases')
    | case :: cases ->
       match_op_case ts t_out case >>= fun case ->
       fold_cases (case :: cases') cases
  in
  fold_cases [] cases

and match_op_case ts t_out (ps, popt, c) =
  let rec fold_args ps_out xts ps ts =
    match ps, ts with

    | [], [] ->
       let ps_out = List.rev ps_out in
       begin match popt with
       | None -> return (None, xts)
       | Some p ->
          let t = Mlty.Apply (Desugar.Builtin.option, [Mlty.Boundary]) in
          check_pattern p t >>= fun (p, xts_p) ->
          return (Some p, xts @ xts_p)
       end >>= fun (popt, xts) ->
       Tyenv.add_bounds_mono xts
         (check_comp c t_out >>= fun c -> return (ps_out, popt, c))

    | p::ps, t::ts ->
       check_pattern p t >>= fun (p, xts_p) ->
       fold_args (p :: ps_out) (xts @ xts_p) ps ts

    | [], _::_ | _::_, [] ->
       assert false
  in
  fold_args [] [] ps ts


and check_comp c t =
  infer_comp c >>= fun (c, t') ->
  Tyenv.add_equation ~at:c.Location.at t' t >>= fun () ->
  return c


and let_clauses
  : 'a . toplevel:bool -> Desugared.let_clause list -> 'a Tyenv.tyenvM ->
         ((Name.t * Mlty.ty_schema) list list * Syntax.let_clause list * 'a) Tyenv.tyenvM
  = fun ~toplevel clauses_in m ->
  let rec fold_rhs cts = function
    | [] -> return (List.rev cts)
    | Desugared.Let_clause (p, annot, c) :: clauses_in ->
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
          | Desugared.Let_annot_schema sch ->
             let sch = ml_schema sch in
             Tyenv.generalizes_to ~at:c.Location.at t sch

          | Desugared.Let_annot_none -> return ()
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
          | Desugared.Let_annot_schema sch ->
             let sch = ml_schema sch in
             begin match sch with
             | ([], tsch) -> Tyenv.add_equation ~at:c.Location.at t tsch
             | (_::_, _) -> Mlty.error ~at:c.Location.at Mlty.ValueRestriction
             end
          | Desugared.Let_annot_none -> return ()
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
         (fold (xss :: info_out) ((Syntax.Let_clause (p, c)) :: clauses_out) clauses_in)
  in
  fold [] [] clauses

and letrec_clauses
  :  'a . toplevel:bool -> Desugared.letrec_clause list ->
          'a Tyenv.tyenvM -> ((Name.t * Mlty.ty_schema) list * Syntax.letrec_clause list * 'a) Tyenv.tyenvM
  = fun ~toplevel fycs m ->

  let bind_functions acc clauses comp_in_extended_context =

    let prepare_types_for_binding a annot =
      let a =
        match a with
        | Desugared.Arg_annot_none -> Mlty.fresh_type ()
        | Desugared.Arg_annot_ty t -> ml_ty [] t
      and b = Mlty.fresh_type () in
      begin
        match annot with
        | Desugared.Let_annot_none ->
           Tyenv.ungeneralize (Mlty.Arrow (a, b)) >>= fun sch ->
           return (sch, None)
        | Desugared.Let_annot_schema sch ->
           let sch = ml_schema sch in
           return (sch, Some sch)
      end >>= fun sch_schopt -> return (a, b, sch_schopt)
    in

    let rec bind_functions_fold acc = function
      | [] -> return (List.rev acc) >>= comp_in_extended_context

      | Desugared.Letrec_clause (f, (y, a), annot, c) :: rem ->
         prepare_types_for_binding a annot >>= fun (a, b, (sch, schopt)) ->
         (if toplevel then Tyenv.add_ml_value_poly else Tyenv.add_bound_poly)
           f sch
           (bind_functions_fold ((f, schopt, y, a, c, b) :: acc) rem)
    in
    bind_functions_fold acc clauses
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
       Tyenv.generalizes_to ~at:c.Location.at t sch >>= fun () ->
       generalize_funs ((f, sch) :: info) (Syntax.Letrec_clause c :: clauses) rem

    | (f, None, y, a, c, b) :: rem ->
       let t = Mlty.Arrow (a, b) in
       Tyenv.generalize t >>= fun sch ->
       generalize_funs ((f, sch) :: info) (Syntax.Letrec_clause c :: clauses) rem

  in

  (* We want [m] to be run in the locally extended context. *)
  bind_functions [] fycs
    begin fun acc ->
      check_bodies [] acc >>=
      generalize_funs [] [] >>= fun (info, clauses) ->
      m >>= fun x ->
      return (info, clauses, x)
    end

  (* bind_functions [] fycs >>=
   * check_bodies [] >>=
   * generalize_funs [] [] >>= fun (info, clauses) ->
   * m >>= fun x ->
   * return (info, clauses, x) *)

and boundary = function
  | Desugared.BoundaryIsType ->
     return Syntax.BoundaryIsType

  | Desugared.BoundaryIsTerm c ->
     check_comp c Mlty.Judgement >>= fun c ->
     return (Syntax.BoundaryIsTerm c)

  | Desugared.BoundaryEqType (c1, c2) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     return (Syntax.BoundaryEqType (c1, c2))

  | Desugared.BoundaryEqTerm (c1, c2, c3) ->
     check_comp c1 Mlty.Judgement >>= fun c1 ->
     check_comp c2 Mlty.Judgement >>= fun c2 ->
     check_comp c3 Mlty.Judgement >>= fun c3 ->
     return (Syntax.BoundaryEqTerm (c1, c2, c3))

and local_context lctx m =
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

and premise {Location.it=prem; at} =
  let Desugared.Premise (x, lctx, bdry) = prem in
  local_context lctx (boundary bdry) >>= fun (lctx, bdry) ->
  let p = locate ~at (Syntax.Premise (x, lctx, bdry)) in
  return (x, p)

and premises :
 'a . Desugared.premise list -> 'a Tyenv.tyenvM -> (Syntax.premise list * 'a) Tyenv.tyenvM
= fun prems m ->
  let rec fold ps = function
    | [] ->
       m >>= fun x ->
       let ps = List.rev ps in return (ps, x)
    | prem :: prems ->
       premise prem >>= fun (x, p) ->
       Tyenv.add_bound_mono x Mlty.Judgement (fold (p::ps) prems)
  in
  fold [] prems

let add_ml_type (t, (params, def)) =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  match def with

    | Desugared.ML_Alias t' ->
       let t' = ml_ty params t' in
       Tyenv.add_ml_type t (Mlty.Alias (params, t'))

    | Desugared.ML_Sum constructors ->
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

let rec toplevel' ({Location.it=c; at} : Desugared.toplevel) =
  match c with

  | Desugared.Rule (rname, prems, bdry) ->
     premises prems (boundary bdry) >>= fun (ps, bdry) ->
     let r = Ident.create rname in
     Tyenv.add_tt_constructor r >>= fun () ->
     return_located ~at (Syntax.Rule (r, ps, bdry))

  | Desugared.DefMLTypeAbstract (t, params) ->
     let params = List.map (fun _ -> Mlty.fresh_param ()) params in
     Tyenv.add_ml_type t (Mlty.Abstract (params, ())) >>= fun () ->
     return_located ~at (Syntax.DefMLTypeAbstract t)

  (* Desugar is the only place where recursion/nonrecursion matters,
     so [DefMLType] and [DefMLTypeRec] behave the same way in typechecking. *)
  | Desugared.DefMLType tydefs ->
     let rec fold = function
       | [] -> return_located ~at (Syntax.DefMLType (List.map fst tydefs))
       | tydef :: tydefs ->
          add_ml_type tydef >>= fun () -> fold tydefs
     in
     fold tydefs

  | Desugared.DefMLTypeRec tydefs ->
     let rec fold = function
       | [] -> return_located ~at (Syntax.DefMLTypeRec (List.map fst tydefs))
       | tydef :: tydefs -> add_ml_type tydef >>= fun () -> fold tydefs
     in
     fold tydefs

  | Desugared.DeclOperation (op, (tys_in, ty_out)) ->
    let tys_in = List.map (ml_ty []) tys_in in
    let ty_out = ml_ty [] ty_out in
    Tyenv.add_ml_operation op (tys_in, ty_out) >>= fun () ->
    return_located ~at (Syntax.DeclOperation (op, (tys_in, ty_out)))

  | Desugared.DeclException (exc, tyopt) ->
    let tyopt =
      match tyopt with
      | None -> None
      | Some ty -> Some (ml_ty [] ty)
    in
    Tyenv.add_ml_exception exc tyopt >>= fun () ->
    return_located ~at (Syntax.DeclException (exc, tyopt))

  | Desugared.DeclExternal (x, sch, s) ->
     let sch = ml_schema sch in
     Tyenv.add_ml_value_poly x sch
        (return_located ~at (Syntax.DeclExternal (x, sch, s)))

  | Desugared.TopLet clauses ->
     let_clauses ~toplevel:true clauses (return ()) >>= fun (info, clauses, ()) ->
     return_located ~at (Syntax.TopLet (info, clauses))

  | Desugared.TopLetRec clauses ->
     letrec_clauses ~toplevel:true clauses (return ()) >>= fun (info, clauses, ()) ->
     return_located ~at (Syntax.TopLetRec (info, clauses))

  | Desugared.TopWith lst ->
     let rec fold lst' = function
       | [] ->
          let lst' = List.rev lst' in
          return_located ~at (Syntax.TopWith lst')
       | (op, case) :: lst ->
          Tyenv.lookup_ml_operation op >>= fun (oid, (ts, t_out)) ->
          match_op_case ts t_out case >>= fun case ->
          fold ((oid, case) :: lst') lst
     in
     fold [] lst

  | Desugared.TopComputation c ->
     infer_comp c >>= fun (c, t) ->
     begin
       match generalizable c with
       | Generalizable ->
          Tyenv.generalize t >>= fun sch ->
          return_located ~at (Syntax.TopComputation (c, sch))
       |  Ungeneralizable ->
          Tyenv.ungeneralize t >>= fun sch ->
          return_located ~at (Syntax.TopComputation (c, sch))
     end

  | Desugared.Verbosity v ->
    return_located ~at (Syntax.Verbosity v)

  | Desugared.Open pth ->
     return_located ~at (Syntax.Open pth)

  | Desugared.MLModule (mdl_name, cs) ->
     Tyenv.as_module (toplevels' cs) >>= fun cs ->
     return_located ~at (Syntax.MLModule (mdl_name, cs))

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
