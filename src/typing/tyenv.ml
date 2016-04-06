module TopEnv = struct
  type t = {
    topctx : Context.t;
    topsubst : Substitution.t;
  }

  let empty = {
    topctx = Context.empty;
    topsubst = Substitution.empty;
  }

  let add_tydef t d env =
    let topctx = Context.add_tydef t d env.topctx in
    {env with topctx}

  let add_operation op opty env =
    let topctx = Context.add_operation op opty env.topctx in
    {env with topctx}

  let gather_known env =
    Mlty.MetaSet.union (Context.gather_known env.topctx) (Substitution.gather_known env.topsubst)

  let add_lets xts env =
    let known = gather_known env in
    let topctx = Context.add_lets xts known env.topsubst env.topctx in
    {env with topctx}
end

module Env = struct
  type t = {
    context : Context.t;
    substitution : Substitution.t;
    unsolved : Context.constrain list;
  }

  let of_topenv {TopEnv.topctx; topsubst} = {
    context = topctx;
    substitution = topsubst;
    unsolved = [];
  }

  type 'a mon = t -> 'a * Substitution.t * Context.constrain list

  let return x env = x, env.substitution, env.unsolved

  let (>>=) m f env =
    let x, substitution, unsolved = m env in
    f x {env with substitution; unsolved}

  let lookup_var k env =
    let t = Context.lookup_var k env.context in
    return t env

  let lookup_op op env =
    return (Context.lookup_op op env.context) env

  let lookup_constructor c env =
    return (Context.lookup_constructor c env.context) env

  let lookup_continuation env =
    return (Context.lookup_continuation env.context) env

  let add_var x t m env =
    let context = Context.add_var x (Mlty.ungeneralized_schema t) env.context in
    m {env with context}

  let gather_known env =
    let known =
      Mlty.MetaSet.union
        (Context.gather_known env.context)
        (Substitution.gather_known env.substitution)
    in
    List.fold_left
      (fun known (Context.AppConstraint (_, t1, t2, t3)) ->
        Mlty.MetaSet.union known
          (Mlty.MetaSet.union
             (Mlty.occuring t1)
             (Mlty.MetaSet.union (Mlty.occuring t2) (Mlty.occuring t3))))
      known env.unsolved

  let add_lets xts m env =
    let known = gather_known env in
    let context = Context.add_lets xts known env.substitution env.context in
    m {env with context}

  (* Whnf for meta instantiations and type aliases *)
  let rec whnf ctx s = function

    | Mlty.Meta m as t ->
      begin match Substitution.lookup m s with
        | Some t -> whnf ctx s t
        | None -> t
      end

    | Mlty.App (_, x, ts) as t ->
      begin match Context.unfold ctx x ts with
        | Some t -> whnf ctx s t
        | None -> t
      end

    | (Mlty.Jdg | Mlty.String | Mlty.Prod _ | Mlty.Arrow _ | Mlty.Handler _ | Mlty.Ref _) as t -> t

  let rec unifiable ctx s t t' =
    let (>?=) m f = match m with
      | Some x -> f x
      | None -> None
    in
    match whnf ctx s t, whnf ctx s t' with

      | Mlty.Jdg, Mlty.Jdg
      | Mlty.String, Mlty.String ->
         Some s

      | Mlty.Meta m, Mlty.Meta m' when m = m' ->
         Some s

      | Mlty.Meta m, t ->
         Substitution.add m t s

      | t, Mlty.Meta m ->
         Substitution.add m t s

      | Mlty.Ref t, Mlty.Ref t' ->
         unifiable ctx s t t'

      | Mlty.Prod ts, Mlty.Prod ts' ->
        let rec fold s ts ts' = match ts, ts' with
          | [], [] -> Some s
          | t :: ts, t' :: ts' ->
            unifiable ctx s t t' >?= fun s ->
            fold s ts ts'
          | [], _ :: _ | _ :: _, [] -> None
        in
        fold s ts ts'

      | Mlty.Arrow (t1, t2), Mlty.Arrow (t1', t2') ->
        unifiable ctx s t1 t1' >?= fun s ->
        unifiable ctx s t2 t2'

      | Mlty.Handler (t1, t2), Mlty.Handler (t1', t2') ->
        unifiable ctx s t1 t1' >?= fun s ->
        unifiable ctx s t2 t2'

      | Mlty.App (_, x, ts), Mlty.App (_, y, ts') when x = y ->
        let rec fold s ts ts' = match ts, ts' with
          | [], [] -> Some s
          | t :: ts, t' :: ts' ->
            unifiable ctx s t t' >?= fun s ->
            fold s ts ts'
          | [], _ :: _ | _ :: _, [] -> assert false
        in
        fold s ts ts'

      | (Mlty.Jdg | Mlty.String | Mlty.Ref _ | Mlty.Prod _ |
         Mlty.Arrow _ | Mlty.Handler _ | Mlty.App _), _ -> None

  let rec add_equation ~loc t t' env =
    match unifiable env.context env.substitution t t' with

      | Some s ->
        let rec fold = function
          | [] -> return ()
          | Context.AppConstraint (loc, h, arg, out) :: unsolved ->
            add_application ~loc h arg out >>= fun () ->
            fold unsolved
        in
        fold env.unsolved {env with substitution=s; unsolved=[]}

      | None ->
         Mlty.error ~loc
           (Mlty.TypeMismatch (Substitution.apply env.substitution t,
                               Substitution.apply env.substitution t'))

  and add_application ~loc h arg out env =
    let s = env.substitution in
    let h = whnf env.context s h
    and arg = whnf env.context s arg
    and out = whnf env.context s out in
    match h with

      | Mlty.Jdg ->
        (>>=) (add_equation ~loc arg Mlty.Jdg) (fun () -> add_equation ~loc out Mlty.Jdg) env

      | Mlty.Arrow (a, b) ->
        (>>=) (add_equation ~loc arg a) (fun () -> add_equation ~loc out b) env

      | Mlty.Meta m ->
         begin
           match arg, out with
           | (Mlty.Jdg | Mlty.Meta _), (Mlty.Jdg | Mlty.Meta _) ->
              let unsolved = Context.AppConstraint (loc, h, arg, out) :: env.unsolved in
              (), s, unsolved
           | _, _ ->
              begin
                match Substitution.add m (Mlty.Arrow (arg, out)) s with
                | Some s ->
                   (), s, env.unsolved
                | None -> Mlty.error ~loc (Mlty.InvalidApplication (h, arg, out))
              end
         end

      | (Mlty.String | Mlty.Ref _ | Mlty.Prod _ |  Mlty.Handler _ | Mlty.App _) ->
         Mlty.error ~loc (Mlty.InvalidApplication (h, arg, out))

  let as_handler ~loc t env =
    let t = whnf env.context env.substitution t in
    match t with

      | Mlty.Handler (a, b) -> return (a, b) env

      | Mlty.Meta m ->
        let a = Mlty.fresh_type ()
        and b = Mlty.fresh_type () in
        begin match Substitution.add m (Mlty.Handler (a, b)) env.substitution with
          | Some substitution -> return (a, b) {env with substitution}
          | None -> assert false
        end

      | (Mlty.Jdg | Mlty.String | Mlty.Ref _ | Mlty.Prod _ | Mlty.Arrow _ | Mlty.App _) ->
         Mlty.error ~loc (Mlty.HandlerExpected t)

  let as_ref ~loc t env =
    let t = whnf env.context env.substitution t in
    match t with

      | Mlty.Ref t -> return t env

      | Mlty.Meta m ->
        let a = Mlty.fresh_type () in
        begin match Substitution.add m (Mlty.Ref a) env.substitution with
          | Some substitution -> return a {env with substitution}
          | None -> assert false
        end

      | (Mlty.Jdg | Mlty.String | Mlty.Prod _ | Mlty.Handler _ | Mlty.Arrow _ | Mlty.App _) ->
         Mlty.error ~loc (Mlty.RefExpected t)

  let op_cases op ~output m env =
    let argts, context = Context.op_cases op ~output env.context in
    m argts {env with context}

  let rec to_solved env =
    match env.unsolved with

      | [] -> {TopEnv.topctx = env.context; topsubst = env.substitution}

      | Context.AppConstraint (loc, arg, h, out) :: unsolved ->
        begin match !Config.appty_guess with
          | Config.NoGuess ->
            let s = env.substitution in
            let h = Substitution.apply s h
            and arg = Substitution.apply s arg
            and out = Substitution.apply s out in
            Mlty.error ~loc (Mlty.UnsolvedApp (arg, h, out))
          | Config.GuessJdg ->
            let (), substitution, unsolved = add_equation ~loc arg Mlty.Jdg env in
            to_solved {env with substitution; unsolved}
          | Config.GuessArrow ->
            let (), substitution, unsolved = add_equation ~loc arg (Mlty.Arrow (h, out)) env in
            to_solved {env with substitution; unsolved}
        end

  let at_toplevel top m =
    let env = of_topenv top in
    let x, substitution, unsolved = m env in
    let top = to_solved {env with substitution; unsolved} in
    x, top

  let predefined_type x ts env =
    let t = Context.predefined_type x ts env.context in
    return t env
end

