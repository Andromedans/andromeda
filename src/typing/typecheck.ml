open Amltype
open Tyenv

let rec tt_pattern xs {Location.thing = p; loc} =
  let (>>=) = Env.(>>=) in
  match p with
  | Syntax.Tt_Anonymous -> Env.return ()

  | Syntax.Tt_As (p, k) ->
    let _, t = List.nth xs k in
    Env.add_equation ~loc t Jdg >>= fun () ->
    tt_pattern xs p

  | Syntax.Tt_Bound k ->
    Env.lookup_var k >>= fun t ->
    Env.add_equation ~loc t Jdg

  | Syntax.Tt_Type -> Env.return ()

  | Syntax.Tt_Constant _ -> Env.return ()

  | Syntax.Tt_Lambda (x, _, popt, p)
  | Syntax.Tt_Prod (x, _, popt, p) ->
    begin match popt with
      | Some pt -> tt_pattern xs pt
      | None -> Env.return ()
    end >>= fun () ->
    Env.add_var x Jdg (tt_pattern xs p)

  | Syntax.Tt_Apply (p1, p2) 
  | Syntax.Tt_Eq (p1, p2) ->
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2

  | Syntax.Tt_Refl p | Syntax.Tt_GenAtom p | Syntax.Tt_GenConstant p ->
    tt_pattern xs p
  

let rec pattern xs {Location.thing = p; loc} =
  let (>>=) = Env.(>>=) in
  match p with
  | Syntax.Patt_Anonymous -> Env.return (fresh_type ())

  | Syntax.Patt_As (p, k) ->
    let _, t = List.nth xs k in
    check_pattern xs p t >>= fun () ->
    Env.return t

  | Syntax.Patt_Bound k -> Env.lookup_var k

  | Syntax.Patt_Jdg (p1, p2) ->
    tt_pattern xs p1 >>= fun () ->
    tt_pattern xs p2 >>= fun () ->
    Env.return Jdg

  | Syntax.Patt_Constructor (c, ps) ->
    Env.lookup_constructor c >>= fun (ts, out) ->
    let tps = List.combine ts ps in
    let rec fold = function
      | [] ->
        Env.return out
      | (t, p) :: tps ->
        check_pattern xs p t >>= fun () ->
        fold tps
    in
    fold tps

  | Syntax.Patt_Tuple ps ->
    let rec fold ts = function
      | [] ->
        let ts = List.rev ts in
        Env.return (Tuple ts)
      | p :: ps ->
        pattern xs p >>= fun t ->
        fold (t :: ts) ps
    in
    fold [] ps

and check_pattern xs p t =
  let (>>=) = Env.(>>=) in
  pattern xs p >>= fun t' ->
  Env.add_equation ~loc:p.Location.loc t' t

let match_case : type a. _ -> _ -> _ -> a Env.mon -> a Env.mon = fun xs p t m ->
  let (>>=) = Env.(>>=) in
  (* add a fresh type to each [x] *)
  let xs = List.map (fun x -> x, fresh_type ()) xs in
  check_pattern xs p t >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | (x, t) :: xs ->
      Env.add_var x t (add_vars xs)
  in
  add_vars (List.rev xs)

let match_op_case xs ps popt argts m =
  let (>>=) = Env.(>>=) in
  let xs = List.map (fun x -> x, fresh_type ()) xs in
  let pts = List.combine ps argts in
  let pts = match popt with
    | Some p -> (p, Jdg) :: pts
    | None -> pts
  in
  let rec fold = function
    | [] -> Env.return ()
    | (p, t) :: pts ->
      check_pattern xs p t >>= fun () ->
      fold pts
  in
  fold pts >>= fun () ->
  let rec add_vars = function
    | [] -> m
    | (x, t) :: xs ->
      Env.add_var x t (add_vars xs)
  in
  add_vars (List.rev xs)

let rec comp ({Location.thing=c; loc} : Syntax.comp) =
  let (>>=) = Env.(>>=) in
  match c with
  | Syntax.Type -> Env.return Jdg

  | Syntax.Bound k -> Env.lookup_var k

  | Syntax.Function (x, c) ->
    let a = fresh_type () in
    Env.add_var x a (comp c) >>= fun b ->
    Env.return (Arrow (a, b))

  | Syntax.Handler h -> handler ~loc h

  | Syntax.Constructor (c, cs) ->
    Env.lookup_constructor c >>= fun (ts, out) ->
    let tcs = List.combine ts cs in
    let rec fold = function
      | [] ->
        Env.return out
      | (t, c) :: tcs ->
        check_comp c t >>= fun () ->
        fold tcs
    in
    fold tcs

  | Syntax.Tuple cs ->
    let rec fold ts = function
      | [] ->
        let ts = List.rev ts in
        Env.return (Tuple ts)
      | c :: cs ->
        comp c >>= fun t ->
        fold (t :: ts) cs
    in
    fold [] cs

  | Syntax.Operation (op, cs) ->
    Env.lookup_op op >>= fun (expected, out) ->
    let tcs = List.combine expected cs in
    let rec fold = function
      | [] ->
        Env.return out
      | (t, c) :: tcs ->
        check_comp c t >>= fun () ->
        fold tcs
    in
    fold tcs

  | Syntax.With (h, c) ->
    comp h >>= fun th ->
    Env.as_handler ~loc:h.Location.loc th >>= fun (a, b) ->
    check_comp c a >>= fun () ->
    Env.return b

  | Syntax.Let (xcs, c) ->
    let rec fold xts = function
      | [] ->
        let xts = List.rev xts in
        Env.return xts
      | (x, c) :: xcs ->
        comp c >>= fun t ->
        let gen = Context.generalizable c in
        fold ((x, gen, t) :: xts) xcs
    in
    fold [] xcs >>= fun xts ->
    Env.add_lets xts (comp c)

  | Syntax.LetRec (xycs, c) ->
    let abxycs = List.map (fun xyc -> fresh_type (), fresh_type (), xyc) xycs in
    let rec fold = function
      | [] -> Env.return ()
      | (a, b, (_, y, c)) :: rem ->
        Env.add_var y a (check_comp c b) >>= fun () ->
        fold rem
    in
    Env.add_lets (List.map (fun (a, b, (x, _, _)) -> x, Context.Ungeneralizable, Arrow (a, b)) abxycs) (fold abxycs) >>= fun () ->
    Env.add_lets (List.map (fun (a, b, (x, _, _)) -> x, Context.Generalizable, Arrow (a, b)) abxycs) (comp c)

  | Syntax.Now (x, c1, c2) ->
    Env.lookup_var x >>= fun tx ->
    check_comp c1 tx >>= fun () ->
    comp c2

  | Syntax.Lookup c ->
    comp c >>= fun t ->
    Env.as_ref ~loc:c.Location.loc t    

  | Syntax.Update (c1, c2) ->
    comp c1 >>= fun t1 ->
    Env.as_ref ~loc:c1.Location.loc t1 >>= fun t ->
    check_comp c2 t >>= fun () ->
    Env.return (Tuple [])

  | Syntax.Ref c ->
    comp c >>= fun t ->
    Env.return (Ref t)

  | Syntax.Sequence (c1, c2) ->
    comp c1 >>= fun _ ->
    (* TODO warn if not unit? *)
    comp c2

  | Syntax.Assume ((x, t), c) ->
    check_comp c Jdg >>= fun () ->
    Env.add_var x Jdg (comp c)

  | Syntax.Where (c1, c2, c3) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    check_comp c3 Jdg >>= fun () ->
    Env.return Jdg

  | Syntax.Match (c, cases) ->
    comp c >>= fun t ->
    match_cases ~loc t cases

  | Syntax.Ascribe (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    Env.return Jdg

  | Syntax.External _ -> Env.return (fresh_type ()) (* TODO *)

  | Syntax.Constant _ -> Env.return Jdg

  | Syntax.Lambda (x, copt, c) ->
    begin match copt with
      | Some ct -> check_comp ct Jdg
      | None -> Env.return ()
    end >>= fun () ->
    Env.add_var x Jdg (check_comp c Jdg) >>= fun () ->
    Env.return Jdg

  | Syntax.Apply (c1, c2) ->
    comp c1 >>= fun t1 ->
    comp c2 >>= fun t2 ->
    let out = fresh_type () in
    Env.add_application ~loc t1 t2 out >>= fun () ->
    Env.return out

  | Syntax.Prod (x, ct, c) ->
    check_comp ct Jdg >>= fun () ->
    Env.add_var x Jdg (check_comp c Jdg) >>= fun () ->
    Env.return Jdg

  | Syntax.Eq (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    Env.return Jdg    

  | Syntax.Refl c ->
    check_comp c Jdg >>= fun () ->
    Env.return Jdg

  | Syntax.Yield c ->
    Env.lookup_continuation >>= fun (a, b) ->
    check_comp c a >>= fun () ->
    Env.return b

  | Syntax.Hypotheses -> assert false (* TODO *)

  | Syntax.Congruence (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    assert false (* TODO *)    

  | Syntax.Extensionality (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    assert false (* TODO *)    

  | Syntax.Reduction c ->
    check_comp c Jdg >>= fun () ->
    assert false (* TODO *)

  | Syntax.String _ -> Env.return String

  | Syntax.Occurs (c1, c2) ->
    check_comp c1 Jdg >>= fun () ->
    check_comp c2 Jdg >>= fun () ->
    assert false (* TODO *)

  | Syntax.Context c ->
    check_comp c Jdg >>= fun () ->
    assert false (* TODO *)    

and check_comp c t =
  let (>>=) = Env.(>>=) in
  comp c >>= fun t' ->
  Env.add_equation ~loc:c.Location.loc t' t

and handler ~loc {Syntax.handler_val=handler_val;handler_ops;handler_finally} =
  let (>>=) = Env.(>>=) in
  let input = fresh_type () in
  begin match handler_val with
    | [] -> Env.return input
    | _ :: _ -> match_cases ~loc input handler_val
  end >>= fun output ->
  begin match handler_finally with
    | [] -> Env.return output
    | _ :: _ -> match_cases ~loc output handler_finally
  end >>= fun final ->
  Name.IdentMap.fold (fun op cases m ->
      m >>= fun () ->
      match_op_cases op cases output)
    handler_ops (Env.return ()) >>= fun () ->
  Env.return (Handler (input, final))

and match_cases ~loc t cases =
  let (>>=) = Env.(>>=) in
  match cases with
    | [] -> assert false (* TODO *)
    | (xs, p, c) :: others ->
      match_case xs p t (comp c) >>= fun out ->
      let rec fold = function
        | [] -> Env.return out
        | (xs, p, c) :: others ->
          match_case xs p t (check_comp c out) >>= fun () ->
          fold others
      in
      fold others

and match_op_cases op cases output =
  let (>>=) = Env.(>>=) in
  Env.op_cases op ~output (fun argts ->
  let rec fold = function
    | [] -> Env.return ()
    | (xs, ps, popt, c) :: cases ->
      match_op_case xs ps popt argts (check_comp c output) >>= fun () ->
      fold cases
  in
  fold cases)

let top_handler ~loc lst =
  let (>>=) = Env.(>>=) in
  let rec fold = function
    | [] -> Env.return ()
    | (op, (xs, y, c)) :: lst ->
      Env.lookup_op op >>= fun (argts, out) ->
      let xts = List.combine xs argts in
      let rec bind = function
        | [] ->
          let bindy m = match y with
            | Some y -> Env.add_var y Jdg m
            | None -> m
          in
          bindy (check_comp c out)
        | (x, t) :: xts ->
          Env.add_var x t (bind xts)
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
    Arrow (t1, t2)
  | Syntax.ML_Prod ts ->
    let ts = List.map (ml_ty params) ts in
    Tuple ts
  | Syntax.ML_TyApply (x, k, ts) ->
    let ts = List.map (ml_ty params) ts in
    App (x, k, ts)
  | Syntax.ML_Handler (t1, t2) ->
    let t1 = ml_ty params t1
    and t2 = ml_ty params t2 in
    Handler (t1, t2)
  | Syntax.ML_Judgment -> Jdg
  | Syntax.ML_Param p -> Meta (List.nth params p)


let add_tydef env (t, (params, def)) =
  let params = List.map (fun _ -> fresh_meta ()) params in
  match def with
    | Syntax.ML_Alias t' ->
      let t' = ml_ty params t' in
      TopEnv.add_tydef t (Alias (params, t')) env
    | Syntax.ML_Sum constructors ->
      let constructors = List.map (fun (c, ts) -> c, List.map (ml_ty params) ts) constructors in
      TopEnv.add_tydef t (Sum (params, constructors)) env

let add_operation op (args, out) env =
  let args = List.map (ml_ty []) args
  and out = ml_ty [] out in
  TopEnv.add_operation op (args, out) env

let rec toplevel env ({Location.thing=c; loc} : Syntax.toplevel) =
  match c with
  (* Desugar is the only place where recursion/nonrecursion matters *)
  | Syntax.DefMLType tydefs
  | Syntax.DefMLTypeRec tydefs ->
    List.fold_left add_tydef env tydefs

  | Syntax.DeclOperation (op, opty) ->
    add_operation op opty env

  | Syntax.DeclConstants (cs, t) ->
    let (), env = Env.at_toplevel env (check_comp t Jdg) in
    env

  | Syntax.TopHandle lst ->
    let (), env = Env.at_toplevel env (top_handler ~loc lst) in
    env

  | Syntax.TopLet xcs ->
    let rec fold xts = function
      | [] ->
        let xts = List.rev xts in
        Env.return xts
      | (x, c) :: xcs ->
        Env.(comp c >>= fun t ->
        let gen = Context.generalizable c in
        fold ((x, gen, t) :: xts) xcs)
    in
    let xts, env = Env.at_toplevel env (fold [] xcs) in
    TopEnv.add_lets xts env

  | Syntax.TopLetRec xycs ->
    let abxycs = List.map (fun xyc -> fresh_type (), fresh_type (), xyc) xycs in
    let rec fold = function
      | [] -> Env.return ()
      | (a, b, (_, y, c)) :: rem ->
        Env.(add_var y a (check_comp c b) >>= fun () ->
        fold rem)
    in
    let (), env = Env.at_toplevel env
      (Env.add_lets (List.map (fun (a, b, (x, _, _)) -> x, Context.Ungeneralizable, Arrow (a, b)) abxycs) (fold abxycs))
    in
    TopEnv.add_lets (List.map (fun (a, b, (x, _, _)) -> x, Context.Generalizable, Arrow (a, b)) abxycs) env

  | Syntax.TopDynamic (x, c) ->
    let t, env = Env.at_toplevel env (comp c) in
    TopEnv.add_lets [x, Context.Ungeneralizable, t] env

  | Syntax.TopNow (x, c) ->
    let (), env = Env.at_toplevel env (Env.(lookup_var x >>= fun tx ->
      check_comp c tx))
    in
    env

  | Syntax.TopDo c ->
    let _, env = Env.at_toplevel env (comp c) in
    env

  | Syntax.TopFail c ->
    let _, env = Env.at_toplevel env (comp c) in
    env

  | Syntax.Verbosity _ -> env

  | Syntax.Included cs ->
     List.fold_left
       (fun env (f, cs) -> List.fold_left toplevel env cs) env cs

