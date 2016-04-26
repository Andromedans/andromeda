
let (>>=) = Tyenv.(>>=)
let return = Tyenv.return

let locate ~loc v = Location.locate v loc

(** Is a computation generalizable *)
type generalizable =
  | Generalizable
  | Ungeneralizable

let rec generalizable c = match c.Location.thing with
(* yes *)
  | Syntax.Bound _ | Syntax.Function _ | Syntax.Handler _ | Syntax.External _ -> Generalizable
  | Syntax.Constructor (_, cs) | Syntax.Tuple cs ->
    if List.for_all (fun c -> generalizable c = Generalizable) cs
    then Generalizable
    else Ungeneralizable

  | Syntax.Let (_, c) | Syntax.LetRec (_, c) | Syntax.Sequence (_, c) ->
    generalizable c

(* no *)
  | _ -> Ungeneralizable

let rec ml_ty params {Location.thing=t; loc} =
  match t with

  | Syntax.ML_Arrow (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Mlty.Arrow (t1, t2)

  | Syntax.ML_Prod ts ->
    let ts = List.map (ml_ty params) ts in
    Mlty.Prod ts

  | Syntax.ML_TyApply (x, k, ts) ->
    let ts = List.map (ml_ty params) ts in
    Mlty.App (x, k, ts)

  | Syntax.ML_Handler (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Mlty.Handler (t1, t2)

  | Syntax.ML_Judgment ->
     Mlty.Jdg

  | Syntax.ML_String ->
     Mlty.String

  | Syntax.ML_Bound p ->
     Mlty.Param (List.nth params p)

  | Syntax.ML_Anonymous ->
     Mlty.fresh_type ()

let ml_schema (Syntax.ML_Forall (params, t)) =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  let t = ml_ty params t in
  (params, t)

let rec tt_pattern xs {Location.thing = p; loc} =
  match p with
  | Syntax.Tt_Anonymous -> Tyenv.return ()

  | Syntax.Tt_As (p, k) ->
    let _, t = List.nth xs k in
    Tyenv.add_equation ~loc t Mlty.Jdg >>= fun () ->
    tt_pattern xs p

  | Syntax.Tt_Bound k ->
    Tyenv.lookup_var k >>= fun t ->
    Tyenv.add_equation ~loc t Mlty.Jdg

  | Syntax.Tt_Type -> Tyenv.return ()

  | Syntax.Tt_Constant _ -> Tyenv.return ()

  | Syntax.Tt_Lambda (x, _, popt, p)
  | Syntax.Tt_Prod (x, _, popt, p) ->
    begin match popt with
      | Some pt -> tt_pattern xs pt
      | None -> Tyenv.return ()
    end >>= fun () ->
    Tyenv.add_var x Mlty.Jdg (tt_pattern xs p)

  | Syntax.Tt_Apply (p1, p2)
  | Syntax.Tt_Eq (p1, p2) ->
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2

  | Syntax.Tt_Refl p | Syntax.Tt_GenAtom p | Syntax.Tt_GenConstant p ->
    tt_pattern xs p


let rec pattern xs {Location.thing = p; loc} =
  match p with
  | Syntax.Patt_Anonymous -> Tyenv.return (Mlty.fresh_type ())

  | Syntax.Patt_As (p, k) ->
    let _, t = List.nth xs k in
    check_pattern xs p t >>= fun () ->
    Tyenv.return t

  | Syntax.Patt_Bound k -> Tyenv.lookup_var k

  | Syntax.Patt_Jdg (p1, p2) ->
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2 >>= fun () ->
    Tyenv.return Mlty.Jdg

  | Syntax.Patt_Constructor (c, ps) ->
    Tyenv.lookup_constructor c >>= fun (ts, out) ->
    let tps = List.combine ts ps in
    let rec fold = function
      | [] ->
        Tyenv.return out
      | (t, p) :: tps ->
        check_pattern xs p t >>= fun () ->
        fold tps
    in
    fold tps

  | Syntax.Patt_Tuple ps ->
    let rec fold ts = function
      | [] ->
        let ts = List.rev ts in
        Tyenv.return (Mlty.Prod ts)
      | p :: ps ->
        pattern xs p >>= fun t ->
        fold (t :: ts) ps
    in
    fold [] ps

and check_pattern xs p t =
  pattern xs p >>= fun t' ->
  Tyenv.add_equation ~loc:p.Location.loc t' t

let match_case xs p t m =
  (* add a fresh type to each [x] *)
  let xs = List.map (fun x -> x, Mlty.fresh_type ()) xs in
  check_pattern xs p t >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | (x, t) :: xs ->
      Tyenv.add_var x t (add_vars xs)
  in
  add_vars (List.rev xs)

let match_op_case xs ps popt argts m =
  let xs = List.map (fun x -> x, Mlty.fresh_type ()) xs in
  let pts = List.combine ps argts in
  begin match popt with
    | Some p -> 
       Tyenv.predefined_type Name.Predefined.option [Mlty.Jdg] >>= fun t ->
       Tyenv.return ((p, t) :: pts)
    | None ->
       Tyenv.return pts
  end >>= fun pts ->
  let rec fold = function
    | [] -> Tyenv.return ()
    | (p, t) :: pts ->
      check_pattern xs p t >>= fun () ->
      fold pts
  in
  fold pts >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | (x, t) :: xs ->
      Tyenv.add_var x t (add_vars xs)
  in
  add_vars (List.rev xs)

let rec comp ({Location.thing=c; loc} : _ Syntax.comp) : (Mlty.ty_schema Syntax.comp * Mlty.ty) Tyenv.tyenvM =
  match c with
  | Syntax.Type ->
    return (locate ~loc Syntax.Type, Mlty.Jdg)

  | Syntax.Bound k ->
    Tyenv.lookup_var k >>= fun t ->
    return (locate ~loc (Syntax.Bound k), t)

  | Syntax.Function (x, c) ->
    let a = Mlty.fresh_type () in
    Tyenv.add_var x a (comp c) >>= fun (c, b) ->
    Tyenv.return (locate ~loc (Syntax.Function (x, c)), Mlty.Arrow (a, b))

  | Syntax.Handler h ->
    handler ~loc h >>= fun (h, t) ->
    return (locate ~loc (Syntax.Handler h), t)

  | Syntax.Constructor (c, cs) ->
    Tyenv.lookup_constructor c >>= fun (ts, out) ->
    let tcs = List.combine ts cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        Tyenv.return (locate ~loc (Syntax.Constructor (c, cs)), out)
      | (t, c) :: tcs ->
        check_comp c t >>= fun c ->
        fold (c :: cs) tcs
    in
    fold [] tcs

  | Syntax.Tuple cs ->
    let rec fold annot ts = function
      | [] ->
        let ts = List.rev ts
        and cs = List.rev annot in
        Tyenv.return (locate ~loc (Syntax.Tuple cs), Mlty.Prod ts)
      | c :: cs ->
        comp c >>= fun (c, t) ->
        fold (c :: annot) (t :: ts) cs
    in
    fold [] [] cs

  | Syntax.Operation (op, cs) ->
    Tyenv.lookup_op op >>= fun (expected, out) ->
    let tcs = List.combine expected cs in
    let rec fold cs = function
      | [] ->
        let cs = List.rev cs in
        Tyenv.return (locate ~loc (Syntax.Operation (op, cs)), out)
      | (t, c) :: tcs ->
        check_comp c t >>= fun c ->
        fold (c :: cs) tcs
    in
    fold [] tcs

  | Syntax.With (h, c) ->
    comp h >>= fun (h, th) ->
    Tyenv.as_handler ~loc:h.Location.loc th >>= fun (a, b) ->
    check_comp c a >>= fun c ->
    Tyenv.return (locate ~loc (Syntax.With (h, c)), b)

  | Syntax.Let (xcs, c) ->
    let_clauses xcs >>= fun clauses ->
    let rec fold = function
      | [] ->
        comp c >>= fun (c, t) ->
        return (locate ~loc (Syntax.Let (clauses, c)), t)
      | (x, s, _) :: rem ->
        Tyenv.add_let x s (fold rem)
    in
    fold clauses

  | Syntax.LetRec (xycs, c) ->
    let_rec_clauses xycs >>= fun clauses ->
    let rec fold = function
      | [] ->
        comp c >>= fun (c, t) ->
        return (locate ~loc (Syntax.LetRec (clauses, c)), t)
      | (x, _, s, _) :: rem ->
        Tyenv.add_let x s (fold rem)
    in
    fold clauses

  | Syntax.Now (x, c1, c2) ->
    Tyenv.lookup_var x >>= fun tx ->
    check_comp c1 tx >>= fun c1 ->
    comp c2 >>= fun (c2, t) ->
    return (locate ~loc (Syntax.Now (x, c1, c2)), t)

  | Syntax.Lookup c ->
    comp c >>= fun (c, t) ->
    Tyenv.as_ref ~loc:c.Location.loc t >>= fun t ->
    return (locate ~loc (Syntax.Lookup c), t)

  | Syntax.Update (c1, c2) ->
    comp c1 >>= fun (c1, t1) ->
    Tyenv.as_ref ~loc:c1.Location.loc t1 >>= fun t ->
    check_comp c2 t >>= fun c2 ->
    Tyenv.return (locate ~loc (Syntax.Update (c1, c2)), Mlty.unit_ty)

  | Syntax.Ref c ->
    comp c >>= fun (c, t) ->
    Tyenv.return (locate ~loc (Syntax.Ref c), Mlty.Ref t)

  | Syntax.Sequence (c1, c2) ->
    comp c1 >>= fun (c1, _) ->
    (* TODO warn if not unit? *)
    comp c2 >>= fun (c2, t) ->
    return (locate ~loc (Syntax.Sequence (c1, c2)), t)

  | Syntax.Assume ((x, a), c) ->
    check_comp a Mlty.Jdg >>= fun a ->
    Tyenv.add_var x Mlty.Jdg (comp c) >>= fun (c, t) ->
    return (locate ~loc (Syntax.Assume ((x, a), c)), t)

  | Syntax.Where (c1, c2, c3) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    check_comp c3 Mlty.Jdg >>= fun c3 ->
    Tyenv.return (locate ~loc (Syntax.Where (c1, c2, c3)), Mlty.Jdg)

  | Syntax.Match (c, cases) ->
    comp c >>= fun (c, tc) ->
    match_cases ~loc tc cases >>= fun (cases, t) ->
    return (locate ~loc (Syntax.Match (c, cases)), t)

  | Syntax.Ascribe (c1, c2) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    Tyenv.return (locate ~loc (Syntax.Ascribe (c1, c2)), Mlty.Jdg)

  | Syntax.External s ->
    begin match External.lookup_ty s with
      | None ->
        Mlty.error ~loc (Mlty.UnknownExternal s)
      | Some (ps, t) ->
         let pus = List.map (fun p -> (p, Mlty.fresh_type ())) ps in
         let t = Mlty.instantiate pus t in
         Tyenv.return (locate ~loc (Syntax.External s), t)
    end

  | Syntax.Constant c -> Tyenv.return (locate ~loc (Syntax.Constant c), Mlty.Jdg)

  | Syntax.Lambda (x, copt, c) ->
    begin match copt with
      | Some ct -> check_comp ct Mlty.Jdg >>= fun ct -> return (Some ct)
      | None -> Tyenv.return None
    end >>= fun copt ->
    Tyenv.add_var x Mlty.Jdg (check_comp c Mlty.Jdg) >>= fun c ->
    Tyenv.return (locate ~loc (Syntax.Lambda (x, copt, c)), Mlty.Jdg)

  | Syntax.Apply (c1, c2) ->
    comp c1 >>= fun (c1, t1) ->
    comp c2 >>= fun (c2, t2) ->
    let out = Mlty.fresh_type () in
    Tyenv.add_application ~loc t1 t2 out >>= fun () ->
    Tyenv.return (locate ~loc (Syntax.Apply (c1, c2)), out)

  | Syntax.Prod (x, ct, c) ->
    check_comp ct Mlty.Jdg >>= fun ct ->
    Tyenv.add_var x Mlty.Jdg (check_comp c Mlty.Jdg) >>= fun c ->
    Tyenv.return (locate ~loc (Syntax.Prod (x, ct, c)), Mlty.Jdg)

  | Syntax.Eq (c1, c2) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    Tyenv.return (locate ~loc (Syntax.Eq (c1, c2)), Mlty.Jdg)

  | Syntax.Refl c ->
    check_comp c Mlty.Jdg >>= fun c ->
    Tyenv.return (locate ~loc (Syntax.Refl c), Mlty.Jdg)

  | Syntax.Yield c ->
    Tyenv.lookup_continuation >>= fun (a, b) ->
    check_comp c a >>= fun c ->
    Tyenv.return (locate ~loc (Syntax.Yield c), b)

  | Syntax.CongrProd (c1, c2, c3) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    check_comp c3 Mlty.Jdg >>= fun c3 ->
    return (locate ~loc (Syntax.CongrProd (c1, c2, c3)), Mlty.Jdg)

  | Syntax.CongrApply (c1, c2, c3, c4, c5) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    check_comp c3 Mlty.Jdg >>= fun c3 ->
    check_comp c4 Mlty.Jdg >>= fun c4 ->
    check_comp c5 Mlty.Jdg >>= fun c5 ->
    return (locate ~loc (Syntax.CongrApply (c1, c2, c3, c4, c5)), Mlty.Jdg)

  | Syntax.CongrLambda (c1, c2, c3, c4) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    check_comp c3 Mlty.Jdg >>= fun c3 ->
    check_comp c4 Mlty.Jdg >>= fun c4 ->
    return (locate ~loc (Syntax.CongrLambda (c1, c2, c3, c4)), Mlty.Jdg)

  | Syntax.CongrEq (c1, c2, c3) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    check_comp c3 Mlty.Jdg >>= fun c3 ->
    return (locate ~loc (Syntax.CongrEq (c1, c2, c3)), Mlty.Jdg)

  | Syntax.CongrRefl (c1, c2) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    return (locate ~loc (Syntax.CongrRefl (c1, c2)), Mlty.Jdg)

  | Syntax.BetaStep (c1, c2, c3, c4, c5) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    check_comp c3 Mlty.Jdg >>= fun c3 ->
    check_comp c4 Mlty.Jdg >>= fun c4 ->
    check_comp c5 Mlty.Jdg >>= fun c5 ->
    return (locate ~loc (Syntax.BetaStep (c1, c2, c3, c4, c5)), Mlty.Jdg)

  | Syntax.String s -> Tyenv.return (locate ~loc (Syntax.String s), Mlty.String)

  | Syntax.Occurs (c1, c2) ->
    check_comp c1 Mlty.Jdg >>= fun c1 ->
    check_comp c2 Mlty.Jdg >>= fun c2 ->
    Tyenv.predefined_type Name.Predefined.option [Mlty.Jdg] >>= fun t ->
    return (locate ~loc (Syntax.Occurs (c1, c2)), t)

  | Syntax.Context c ->
    check_comp c Mlty.Jdg >>= fun c ->
    Tyenv.predefined_type Name.Predefined.list [Mlty.Jdg] >>= fun t ->
    return (locate ~loc (Syntax.Context c), t)

  | Syntax.Natural c ->
    check_comp c Mlty.Jdg >>= fun c ->
    return (locate ~loc (Syntax.Natural c), Mlty.Jdg)

and check_comp c t =
  comp c >>= fun (c, t') ->
  Tyenv.add_equation ~loc:c.Location.loc t' t >>= fun () ->
  return c

and handler ~loc {Syntax.handler_val=handler_val;handler_ops;handler_finally} =
  let input = Mlty.fresh_type () in
  begin match handler_val with
    | [] -> Tyenv.return ([], input)
    | _ :: _ -> match_cases ~loc input handler_val
  end >>= fun (handler_val, output) ->
  begin match handler_finally with
    | [] -> Tyenv.return ([], output)
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
  Tyenv.return ({Syntax.handler_val=handler_val;handler_ops;handler_finally}, Mlty.Handler (input, final))

and match_cases ~loc t cases =
  match cases with
    | [] ->
      Tyenv.predefined_type Name.Predefined.empty [] >>= fun empty ->
      Tyenv.add_equation ~loc t empty >>= fun () ->
      Tyenv.return ([], Mlty.fresh_type ())
    | (xs, p, c) :: others ->
      match_case xs p t (comp c) >>= fun (c, out) ->
      let rec fold cases = function
        | [] ->
          let cases = List.rev cases in
          Tyenv.return (cases, out)
        | (xs, p, c) :: others ->
          match_case xs p t (check_comp c out) >>= fun c ->
          fold ((xs, p, c) :: cases) others
      in
      fold [xs, p, c] others

and match_op_cases op cases output =
  Tyenv.op_cases op ~output (fun argts ->
  let rec fold cases = function
    | [] -> Tyenv.return (List.rev cases)
    | (xs, ps, popt, c) :: rem ->
      match_op_case xs ps popt argts (check_comp c output) >>= fun c ->
      fold ((xs, ps, popt, c) :: cases) rem
  in
  fold [] cases)

and let_clauses (xcs : _ Syntax.let_clause list) : Mlty.ty_schema Syntax.let_clause list Tyenv.tyenvM =
  let rec fold xs = function

    | [] -> Tyenv.return (List.rev xs)

    | (x, None, c) :: xcs ->
      comp c >>= fun (c, t) ->
      begin
        match generalizable c with
        | Generalizable -> Tyenv.generalize t
        | Ungeneralizable -> Tyenv.return (Mlty.ungeneralized_schema t)
      end >>= fun sch ->
      Tyenv.normalize_schema sch >>= fun sch ->
      fold ((x, sch, c) :: xs) xcs

    | (x, Some {Location.thing=sch; _}, c) :: xcs ->
      let sch = ml_schema sch in
      comp c >>= fun (c, t) ->
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
       end >>= fun () ->
       fold ((x, sch, c) :: xs) xcs
  in
  fold [] xcs

and let_rec_clauses (fycs : _ Syntax.letrec_clause list) : Mlty.ty_schema Syntax.letrec_clause list Tyenv.tyenvM =
  let rec bind_functions acc = function
    | (f, y, None, c) :: rem ->
       let a = Mlty.fresh_type ()
       and b = Mlty.fresh_type () in
       let sch = Mlty.ungeneralized_schema (Mlty.Arrow (a, b)) in
       Tyenv.add_let f sch (bind_functions ((f, None, y, a, c, b) :: acc) rem)
       
    | (f, y, Some sch, c) :: rem ->
       let sch = ml_schema sch.Location.thing in
       let a = Mlty.fresh_type ()
       and b = Mlty.fresh_type () in
       Tyenv.add_let f sch (bind_functions ((f, Some sch, y, a, c, b) :: acc) rem)

    | [] -> 
       let rec check_bodies acc = function
         | [] -> Tyenv.return (List.rev acc)

         | (f, schopt, y, a, c, b) :: rem ->
            Tyenv.add_var y a (check_comp c b) >>= fun c ->
            check_bodies ((f, schopt, y, a, c, b) :: acc) rem
       in
       check_bodies [] (List.rev acc)
  in
  bind_functions [] fycs >>= fun lst ->
  let rec fold acc = function
    | [] -> Tyenv.return (List.rev acc)

    | (f, Some sch, y, a, c, b) :: rem ->
       let t = Mlty.Arrow (a, b) in
       Tyenv.generalizes_to ~loc:c.Location.loc t sch >>= fun () ->
       fold ((f, y, sch, c) :: acc) rem

    | (f, None, y, a, c, b) :: rem ->
       let t = Mlty.Arrow (a, b) in
       Tyenv.generalize t >>= fun sch ->
       Tyenv.normalize_schema sch >>= fun sch ->
       fold ((f, y, sch, c) :: acc) rem
  in
  fold [] lst

let top_handler ~loc lst =
  let rec fold cases = function
    | [] -> Tyenv.return (List.rev cases)
    | (op, (xs, y, c)) :: lst ->
      Tyenv.lookup_op op >>= fun (argts, out) ->
      let xts = List.combine xs argts in
      let rec bind = function
        | [] ->
          let bindy m = match y with
            | Some y -> 
               Tyenv.predefined_type Name.Predefined.option [Mlty.Jdg] >>= fun jdg_opt ->
               Tyenv.add_var y jdg_opt m
            | None -> m
          in
          bindy (check_comp c out)
        | (x, t) :: xts ->
          Tyenv.add_var x t (bind xts)
      in
      bind xts >>= fun c ->
      fold ((op, (xs, y, c)) :: cases) lst
  in
  fold [] lst

let add_tydef env (t, (params, def)) =
  let params = List.map (fun _ -> Mlty.fresh_param ()) params in
  match def with

    | Syntax.ML_Alias t' ->
       let t' = ml_ty params t' in
       Tyenv.topadd_tydef t (Mlty.Alias (params, t')) env

    | Syntax.ML_Sum constructors ->
       let constructors = List.map (fun (c, ts) -> c, List.map (ml_ty params) ts) constructors in
       Tyenv.topadd_tydef t (Mlty.Sum (params, constructors)) env

let add_operation op (args, out) env =
  let args = List.map (ml_ty []) args
  and out = ml_ty [] out in
  Tyenv.topadd_operation op (args, out) env

let rec toplevel env ({Location.thing=c; loc} : _ Syntax.toplevel) =
  match c with
  (* Desugar is the only place where recursion/nonrecursion matters *)
  | Syntax.DefMLType tydefs ->
    let env = List.fold_left add_tydef env tydefs in
    env, locate ~loc (Syntax.DefMLType tydefs)

  | Syntax.DefMLTypeRec tydefs ->
    let env = List.fold_left add_tydef env tydefs in
    env, locate ~loc (Syntax.DefMLTypeRec tydefs)

  | Syntax.DeclOperation (op, opty) ->
    let env = add_operation op opty env in
    env, locate ~loc (Syntax.DeclOperation (op, opty))

  | Syntax.DeclConstants (cs, t) ->
    let env, t = Tyenv.at_toplevel env (check_comp t Mlty.Jdg) in
    env, locate ~loc (Syntax.DeclConstants (cs, t))

  | Syntax.TopHandle lst ->
    let env, lst = Tyenv.at_toplevel env (top_handler ~loc lst) in
    env, locate ~loc (Syntax.TopHandle lst)

  | Syntax.TopLet xcs ->
    let env, xcs = Tyenv.at_toplevel env (let_clauses xcs) in
    let env = List.fold_left (fun env (x, s, _) -> Tyenv.topadd_let x s env) env xcs in
    env, locate ~loc (Syntax.TopLet xcs)

  | Syntax.TopLetRec xycs ->
    let env, xycs = Tyenv.at_toplevel env (let_rec_clauses xycs) in
    let env = List.fold_left (fun env (x, _, s, _) -> Tyenv.topadd_let x s env) env xycs in
    env, locate ~loc (Syntax.TopLetRec xycs)

  | Syntax.TopDynamic (x, _, c) ->
    let env, (c, t) = Tyenv.at_toplevel env (comp c) in
    let s = Mlty.ungeneralized_schema t in
    let env = Tyenv.topadd_let x s env in
    env, locate ~loc (Syntax.TopDynamic (x, s, c))

  | Syntax.TopNow (x, c) ->
    let env, c = Tyenv.at_toplevel env (Tyenv.lookup_var x >>= fun tx ->
      check_comp c tx)
    in
    env, locate ~loc (Syntax.TopNow (x, c))

  | Syntax.TopDo c ->
    let env, (c, _) = Tyenv.at_toplevel env (comp c) in
    env, locate ~loc (Syntax.TopDo c)

  | Syntax.TopFail c ->
    let env, (c, _) = Tyenv.at_toplevel env (comp c) in
    env, locate ~loc (Syntax.TopFail c)

  | Syntax.Verbosity v ->
    env, locate ~loc (Syntax.Verbosity v)

  | Syntax.Included fcs ->
    let rec fold_files env fcs = function
      | [] ->
        let fcs = List.rev fcs in
        env, fcs
      | (f, cs) :: rem ->
        let env, cs = List.fold_left (fun (env, cs) c ->
            let env, c = toplevel env c in
            (env, c :: cs))
          (env, []) cs
        in
        let cs = List.rev cs in
        fold_files env ((f, cs) :: fcs) rem
    in
    let env, fcs = fold_files env [] fcs in
    env, locate ~loc (Syntax.Included fcs)

