let rec tt_pattern xs {Location.thing = p; loc} =
  let (>>=) = Tyenv.Env.(>>=) in
  match p with
  | Syntax.Tt_Anonymous -> Tyenv.Env.return ()

  | Syntax.Tt_As (p, k) ->
    let _, t = List.nth xs k in
    Tyenv.Env.add_equation ~loc t Mlty.Jdg >>= fun () ->
    tt_pattern xs p

  | Syntax.Tt_Bound k ->
    Tyenv.Env.lookup_var k >>= fun t ->
    Tyenv.Env.add_equation ~loc t Mlty.Jdg

  | Syntax.Tt_Type -> Tyenv.Env.return ()

  | Syntax.Tt_Constant _ -> Tyenv.Env.return ()

  | Syntax.Tt_Lambda (x, _, popt, p)
  | Syntax.Tt_Prod (x, _, popt, p) ->
    begin match popt with
      | Some pt -> tt_pattern xs pt
      | None -> Tyenv.Env.return ()
    end >>= fun () ->
    Tyenv.Env.add_var x Mlty.Jdg (tt_pattern xs p)

  | Syntax.Tt_Apply (p1, p2)
  | Syntax.Tt_Eq (p1, p2) ->
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2

  | Syntax.Tt_Refl p | Syntax.Tt_GenAtom p | Syntax.Tt_GenConstant p ->
    tt_pattern xs p


let rec pattern xs {Location.thing = p; loc} =
  let (>>=) = Tyenv.Env.(>>=) in
  match p with
  | Syntax.Patt_Anonymous -> Tyenv.Env.return (Mlty.fresh_type ())

  | Syntax.Patt_As (p, k) ->
    let _, t = List.nth xs k in
    check_pattern xs p t >>= fun () ->
    Tyenv.Env.return t

  | Syntax.Patt_Bound k -> Tyenv.Env.lookup_var k

  | Syntax.Patt_Jdg (p1, p2) ->
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2 >>= fun () ->
    Tyenv.Env.return Mlty.Jdg

  | Syntax.Patt_Constructor (c, ps) ->
    Tyenv.Env.lookup_constructor c >>= fun (ts, out) ->
    let tps = List.combine ts ps in
    let rec fold = function
      | [] ->
        Tyenv.Env.return out
      | (t, p) :: tps ->
        check_pattern xs p t >>= fun () ->
        fold tps
    in
    fold tps

  | Syntax.Patt_Tuple ps ->
    let rec fold ts = function
      | [] ->
        let ts = List.rev ts in
        Tyenv.Env.return (Mlty.Prod ts)
      | p :: ps ->
        pattern xs p >>= fun t ->
        fold (t :: ts) ps
    in
    fold [] ps

and check_pattern xs p t =
  let (>>=) = Tyenv.Env.(>>=) in
  pattern xs p >>= fun t' ->
  Tyenv.Env.add_equation ~loc:p.Location.loc t' t

let match_case : type a. _ -> _ -> _ -> a Tyenv.Env.mon -> a Tyenv.Env.mon = fun xs p t m ->
  let (>>=) = Tyenv.Env.(>>=) in
  (* add a fresh type to each [x] *)
  let xs = List.map (fun x -> x, Mlty.fresh_type ()) xs in
  check_pattern xs p t >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | (x, t) :: xs ->
      Tyenv.Env.add_var x t (add_vars xs)
  in
  add_vars (List.rev xs)

let match_op_case xs ps popt argts m =
  let (>>=) = Tyenv.Env.(>>=) in
  let xs = List.map (fun x -> x, Mlty.fresh_type ()) xs in
  let pts = List.combine ps argts in
  let pts = match popt with
    | Some p -> (p, Mlty.Jdg) :: pts
    | None -> pts
  in
  let rec fold = function
    | [] -> Tyenv.Env.return ()
    | (p, t) :: pts ->
      check_pattern xs p t >>= fun () ->
      fold pts
  in
  fold pts >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | (x, t) :: xs ->
      Tyenv.Env.add_var x t (add_vars xs)
  in
  add_vars (List.rev xs)

let rec comp ({Location.thing=c; loc} : Syntax.comp) =
  let (>>=) = Tyenv.Env.(>>=) in
  match c with
  | Syntax.Type -> Tyenv.Env.return Mlty.Jdg

  | Syntax.Bound k -> Tyenv.Env.lookup_var k

  | Syntax.Function (x, c) ->
    let a = Mlty.fresh_type () in
    Tyenv.Env.add_var x a (comp c) >>= fun b ->
    Tyenv.Env.return (Mlty.Arrow (a, b))

  | Syntax.Handler h -> handler ~loc h

  | Syntax.Constructor (c, cs) ->
    Tyenv.Env.lookup_constructor c >>= fun (ts, out) ->
    let tcs = List.combine ts cs in
    let rec fold = function
      | [] ->
        Tyenv.Env.return out
      | (t, c) :: tcs ->
        check_comp c t >>= fun () ->
        fold tcs
    in
    fold tcs

  | Syntax.Tuple cs ->
    let rec fold ts = function
      | [] ->
        let ts = List.rev ts in
        Tyenv.Env.return (Mlty.Prod ts)
      | c :: cs ->
        comp c >>= fun t ->
        fold (t :: ts) cs
    in
    fold [] cs

  | Syntax.Operation (op, cs) ->
    Tyenv.Env.lookup_op op >>= fun (expected, out) ->
    let tcs = List.combine expected cs in
    let rec fold = function
      | [] ->
        Tyenv.Env.return out
      | (t, c) :: tcs ->
        check_comp c t >>= fun () ->
        fold tcs
    in
    fold tcs

  | Syntax.With (h, c) ->
    comp h >>= fun th ->
    Tyenv.Env.as_handler ~loc:h.Location.loc th >>= fun (a, b) ->
    check_comp c a >>= fun () ->
    Tyenv.Env.return b

  | Syntax.Let (xcs, c) ->
    let rec fold xts = function
      | [] ->
        let xts = List.rev xts in
        Tyenv.Env.return xts
      | (x, c) :: xcs ->
        comp c >>= fun t ->
        let gen = Context.generalizable c in
        fold ((x, gen, t) :: xts) xcs
    in
    fold [] xcs >>= fun xts ->
    Tyenv.Env.add_lets xts (comp c)

  | Syntax.LetRec (xycs, c) ->
    let abxycs =
      List.map (fun xyc -> Mlty.fresh_type (), Mlty.fresh_type (), xyc) xycs
    in
    let rec fold = function
      | [] -> Tyenv.Env.return ()
      | (a, b, (_, y, c)) :: rem ->
        Tyenv.Env.add_var y a (check_comp c b) >>= fun () ->
        fold rem
    in
    Tyenv.Env.add_lets
      (List.map (fun (a, b, (x, _, _)) -> x, Context.Ungeneralizable, Mlty.Arrow (a, b)) abxycs)
      (fold abxycs)
    >>= fun () ->
    Tyenv.Env.add_lets
      (List.map (fun (a, b, (x, _, _)) -> x, Context.Generalizable, Mlty.Arrow (a, b)) abxycs)
      (comp c)

  | Syntax.Now (x, c1, c2) ->
    Tyenv.Env.lookup_var x >>= fun tx ->
    check_comp c1 tx >>= fun () ->
    comp c2

  | Syntax.Lookup c ->
    comp c >>= fun t ->
    Tyenv.Env.as_ref ~loc:c.Location.loc t

  | Syntax.Update (c1, c2) ->
    comp c1 >>= fun t1 ->
    Tyenv.Env.as_ref ~loc:c1.Location.loc t1 >>= fun t ->
    check_comp c2 t >>= fun () ->
    Tyenv.Env.return Mlty.unit_ty

  | Syntax.Ref c ->
    comp c >>= fun t ->
    Tyenv.Env.return (Mlty.Ref t)

  | Syntax.Sequence (c1, c2) ->
    comp c1 >>= fun _ ->
    (* TODO warn if not unit? *)
    comp c2

  | Syntax.Assume ((x, t), c) ->
    check_comp c Mlty.Jdg >>= fun () ->
    Tyenv.Env.add_var x Mlty.Jdg (comp c)

  | Syntax.Where (c1, c2, c3) ->
    check_comp c1 Mlty.Jdg >>= fun () ->
    check_comp c2 Mlty.Jdg >>= fun () ->
    check_comp c3 Mlty.Jdg >>= fun () ->
    Tyenv.Env.return Mlty.Jdg

  | Syntax.Match (c, cases) ->
    comp c >>= fun t ->
    match_cases ~loc t cases

  | Syntax.Ascribe (c1, c2) ->
    check_comp c1 Mlty.Jdg >>= fun () ->
    check_comp c2 Mlty.Jdg >>= fun () ->
    Tyenv.Env.return Mlty.Jdg

  | Syntax.External s ->
    begin match External.lookup_ty s with
      | None ->
        Mlty.error ~loc (Mlty.UnknownExternal s)
      | Some (ms, t) ->
        let subst, _ = Substitution.freshen_metas ms in
        let t = Substitution.apply subst t in
        Tyenv.Env.return t
    end

  | Syntax.Constant _ -> Tyenv.Env.return Mlty.Jdg

  | Syntax.Lambda (x, copt, c) ->
    begin match copt with
      | Some ct -> check_comp ct Mlty.Jdg
      | None -> Tyenv.Env.return ()
    end >>= fun () ->
    Tyenv.Env.add_var x Mlty.Jdg (check_comp c Mlty.Jdg) >>= fun () ->
    Tyenv.Env.return Mlty.Jdg

  | Syntax.Apply (c1, c2) ->
    comp c1 >>= fun t1 ->
    comp c2 >>= fun t2 ->
    let out = Mlty.fresh_type () in
    Tyenv.Env.add_application ~loc t1 t2 out >>= fun () ->
    Tyenv.Env.return out

  | Syntax.Prod (x, ct, c) ->
    check_comp ct Mlty.Jdg >>= fun () ->
    Tyenv.Env.add_var x Mlty.Jdg (check_comp c Mlty.Jdg) >>= fun () ->
    Tyenv.Env.return Mlty.Jdg

  | Syntax.Eq (c1, c2) ->
    check_comp c1 Mlty.Jdg >>= fun () ->
    check_comp c2 Mlty.Jdg >>= fun () ->
    Tyenv.Env.return Mlty.Jdg

  | Syntax.Refl c ->
    check_comp c Mlty.Jdg >>= fun () ->
    Tyenv.Env.return Mlty.Jdg

  | Syntax.Yield c ->
    Tyenv.Env.lookup_continuation >>= fun (a, b) ->
    check_comp c a >>= fun () ->
    Tyenv.Env.return b

  | Syntax.Hypotheses ->
    Tyenv.Env.predefined_type Name.Predefined.list [Mlty.Jdg]

  | Syntax.Congruence (c1, c2) ->
    check_comp c1 Mlty.Jdg >>= fun () ->
    check_comp c2 Mlty.Jdg >>= fun () ->
    Tyenv.Env.predefined_type Name.Predefined.option [Mlty.Jdg]

  | Syntax.Extensionality (c1, c2) ->
    check_comp c1 Mlty.Jdg >>= fun () ->
    check_comp c2 Mlty.Jdg >>= fun () ->
    Tyenv.Env.predefined_type Name.Predefined.option [Mlty.Jdg]

  | Syntax.Reduction c ->
    check_comp c Mlty.Jdg >>= fun () ->
    Tyenv.Env.predefined_type Name.Predefined.option [Mlty.Jdg]

  | Syntax.String _ -> Tyenv.Env.return Mlty.String

  | Syntax.Occurs (c1, c2) ->
    check_comp c1 Mlty.Jdg >>= fun () ->
    check_comp c2 Mlty.Jdg >>= fun () ->
    Tyenv.Env.predefined_type Name.Predefined.option [Mlty.Jdg]

  | Syntax.Context c ->
    check_comp c Mlty.Jdg >>= fun () ->
    Tyenv.Env.predefined_type Name.Predefined.list [Mlty.Jdg]

and check_comp c t =
  let (>>=) = Tyenv.Env.(>>=) in
  comp c >>= fun t' ->
  Tyenv.Env.add_equation ~loc:c.Location.loc t' t

and handler ~loc {Syntax.handler_val=handler_val;handler_ops;handler_finally} =
  let (>>=) = Tyenv.Env.(>>=) in
  let input = Mlty.fresh_type () in
  begin match handler_val with
    | [] -> Tyenv.Env.return input
    | _ :: _ -> match_cases ~loc input handler_val
  end >>= fun output ->
  begin match handler_finally with
    | [] -> Tyenv.Env.return output
    | _ :: _ -> match_cases ~loc output handler_finally
  end >>= fun final ->
  Name.IdentMap.fold (fun op cases m ->
      m >>= fun () ->
      match_op_cases op cases output)
    handler_ops (Tyenv.Env.return ()) >>= fun () ->
  Tyenv.Env.return (Mlty.Handler (input, final))

and match_cases ~loc t cases =
  let (>>=) = Tyenv.Env.(>>=) in
  match cases with
    | [] ->
      Tyenv.Env.predefined_type Name.Predefined.empty [] >>= fun empty ->
      Tyenv.Env.add_equation ~loc t empty >>= fun () ->
      Tyenv.Env.return (Mlty.fresh_type ())
    | (xs, p, c) :: others ->
      match_case xs p t (comp c) >>= fun out ->
      let rec fold = function
        | [] -> Tyenv.Env.return out
        | (xs, p, c) :: others ->
          match_case xs p t (check_comp c out) >>= fun () ->
          fold others
      in
      fold others

and match_op_cases op cases output =
  let (>>=) = Tyenv.Env.(>>=) in
  Tyenv.Env.op_cases op ~output (fun argts ->
  let rec fold = function
    | [] -> Tyenv.Env.return ()
    | (xs, ps, popt, c) :: cases ->
      match_op_case xs ps popt argts (check_comp c output) >>= fun () ->
      fold cases
  in
  fold cases)

let top_handler ~loc lst =
  let (>>=) = Tyenv.Env.(>>=) in
  let rec fold = function
    | [] -> Tyenv.Env.return ()
    | (op, (xs, y, c)) :: lst ->
      Tyenv.Env.lookup_op op >>= fun (argts, out) ->
      let xts = List.combine xs argts in
      let rec bind = function
        | [] ->
          let bindy m = match y with
            | Some y -> Tyenv.Env.add_var y Mlty.Jdg m
            | None -> m
          in
          bindy (check_comp c out)
        | (x, t) :: xts ->
          Tyenv.Env.add_var x t (bind xts)
      in
      bind xts >>= fun () ->
      fold lst
  in
  fold lst

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

  | Syntax.ML_Param p ->
     Mlty.Meta (List.nth params p)


let add_tydef env (t, (params, def)) =
  let params = List.map (fun _ -> Mlty.fresh_meta ()) params in
  match def with

    | Syntax.ML_Alias t' ->
       let t' = ml_ty params t' in
       Tyenv.TopEnv.add_tydef t (Mlty.Alias (params, t')) env

    | Syntax.ML_Sum constructors ->
       let constructors = List.map (fun (c, ts) -> c, List.map (ml_ty params) ts) constructors in
       Tyenv.TopEnv.add_tydef t (Mlty.Sum (params, constructors)) env

let add_operation op (args, out) env =
  let args = List.map (ml_ty []) args
  and out = ml_ty [] out in
  Tyenv.TopEnv.add_operation op (args, out) env

let rec toplevel ~quiet env ({Location.thing=c; loc} : Syntax.toplevel) =
  match c with
  (* Desugar is the only place where recursion/nonrecursion matters *)
  | Syntax.DefMLType tydefs
  | Syntax.DefMLTypeRec tydefs ->
    List.fold_left add_tydef env tydefs

  | Syntax.DeclOperation (op, opty) ->
    add_operation op opty env

  | Syntax.DeclConstants (cs, t) ->
    let (), env = Tyenv.Env.at_toplevel env (check_comp t Mlty.Jdg) in
    env

  | Syntax.TopHandle lst ->
    let (), env = Tyenv.Env.at_toplevel env (top_handler ~loc lst) in
    env

  | Syntax.TopLet xcs ->
    let rec fold xts = function
      | [] ->
        let xts = List.rev xts in
        Tyenv.Env.return xts
      | (x, c) :: xcs ->
        Tyenv.Env.(comp c >>= fun t ->
        let gen = Context.generalizable c in
        fold ((x, gen, t) :: xts) xcs)
    in
    let xts, env = Tyenv.Env.at_toplevel env (fold [] xcs) in
    if not quiet then
      List.iter (fun (x, _, t) -> Format.printf "%t : %t@."
                                  (Name.print_ident x)
                                  (Mlty.print_ty ~penv:(Mlty.fresh_penv ()) t))
                xts ;
    Tyenv.TopEnv.add_lets xts env

  | Syntax.TopLetRec xycs ->
    let abxycs = List.map (fun xyc -> Mlty.fresh_type (), Mlty.fresh_type (), xyc) xycs in
    let rec fold = function
      | [] -> Tyenv.Env.return ()
      | (a, b, (_, y, c)) :: rem ->
        Tyenv.Env.(add_var y a (check_comp c b) >>= fun () ->
        fold rem)
    in
    let (), env =
      Tyenv.Env.at_toplevel env
        (Tyenv.Env.add_lets
           (List.map (fun (a, b, (x, _, _)) -> x, Context.Ungeneralizable, Mlty.Arrow (a, b)) abxycs)
           (fold abxycs))
    in
    Tyenv.TopEnv.add_lets
      (List.map (fun (a, b, (x, _, _)) -> x, Context.Generalizable, Mlty.Arrow (a, b)) abxycs)
      env

  | Syntax.TopDynamic (x, c) ->
    let t, env = Tyenv.Env.at_toplevel env (comp c) in
    Tyenv.TopEnv.add_lets [x, Context.Ungeneralizable, t] env

  | Syntax.TopNow (x, c) ->
    let (), env = Tyenv.Env.at_toplevel env (Tyenv.Env.(lookup_var x >>= fun tx ->
      check_comp c tx))
    in
    env

  | Syntax.TopDo c ->
    let _, env = Tyenv.Env.at_toplevel env (comp c) in
    env

  | Syntax.TopFail c ->
    let _, env = Tyenv.Env.at_toplevel env (comp c) in
    env

  | Syntax.Verbosity _ -> env

  | Syntax.Included cs ->
     List.fold_left
       (fun env (f, cs) -> List.fold_left (toplevel ~quiet) env cs) env cs

