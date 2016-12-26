type constrain =
  | AppConstraint of Location.t * Mlty.ty * Mlty.ty * Mlty.ty

type t =
  { context : Context.t;
    substitution : Substitution.t;
    unsolved : constrain list }

type 'a tyenvM = t -> 'a * Substitution.t * constrain list

let empty =
  { context = Context.empty;
    substitution = Substitution.empty;
    unsolved = [] }

let return x env = x, env.substitution, env.unsolved

let (>>=) m f env =
  let x, substitution, unsolved = m env in
  f x {env with substitution; unsolved}

let unsolved_known unsolved =
  List.fold_left
    (fun known (AppConstraint (_, t1, t2, t3)) ->
      Mlty.MetaSet.union known
                         (Mlty.MetaSet.union
                            (Mlty.occuring t1)
                            (Mlty.MetaSet.union (Mlty.occuring t2) (Mlty.occuring t3))))
    Mlty.MetaSet.empty unsolved

let gather_known env =
  Mlty.MetaSet.union
    (Mlty.MetaSet.union
       (Context.gather_known env.substitution env.context)
       (Substitution.domain env.substitution))
    (unsolved_known env.unsolved)

let remove_known ~known s =
  Mlty.MetaSet.fold Mlty.MetaSet.remove known s

let generalize t env =
  let known = gather_known env in
  let t = Substitution.apply env.substitution t in
  let gen = Mlty.occuring t in
  let gen = remove_known ~known gen in
  let gen = Mlty.MetaSet.elements gen in
  let ps = List.map (fun _ -> Mlty.fresh_param ()) gen in
  let s = Substitution.from_lists gen (List.map (fun p -> Mlty.Param p) ps) in
  let t = Substitution.apply s t in
  return (ps, t) env

let add_let x s m env =
  let context = Context.add_let x s env.context in
  m {env with context}

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

  | (Mlty.Judgment | Mlty.String | Mlty.Param _ | Mlty.Prod _ | Mlty.Arrow _ |
     Mlty.Handler _ | Mlty.Ref _ | Mlty.Dynamic _) as t -> t

let rec unifiable ctx s t t' =
  let (>?=) m f = match m with
    | Some x -> f x
    | None -> None
  in
  match whnf ctx s t, whnf ctx s t' with

  | Mlty.Judgment, Mlty.Judgment
  | Mlty.String, Mlty.String ->
     Some s

  | Mlty.Meta m, Mlty.Meta m' when m = m' ->
     Some s

  | Mlty.Meta m, t ->
     Substitution.add m t s

  | t, Mlty.Meta m ->
     Substitution.add m t s

  | Mlty.Param p, Mlty.Param p' when p = p' ->
     Some s

  | Mlty.Ref t, Mlty.Ref t' ->
     unifiable ctx s t t'

  | Mlty.Dynamic t, Mlty.Dynamic t' ->
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

  | (Mlty.Judgment | Mlty.String | Mlty.Ref _ | Mlty.Dynamic _ | Mlty.Prod _ | Mlty.Param _ |
     Mlty.Arrow _ | Mlty.Handler _ | Mlty.App _), _ -> None

let rec add_equation ~loc t t' env =
  match unifiable env.context env.substitution t t' with

  | Some s ->
     let rec fold = function
       | [] -> return ()
       | AppConstraint (loc, h, arg, out) :: unsolved ->
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

  | Mlty.Judgment ->
     (>>=) (add_equation ~loc arg Mlty.Judgment) (fun () -> add_equation ~loc out Mlty.Judgment) env

  | Mlty.Arrow (a, b) ->
     (>>=) (add_equation ~loc arg a) (fun () -> add_equation ~loc out b) env

  | Mlty.Meta m ->
     begin
       match arg, out with
       | (Mlty.Judgment | Mlty.Meta _), (Mlty.Judgment | Mlty.Meta _) ->
          let unsolved = AppConstraint (loc, h, arg, out) :: env.unsolved in
          (), s, unsolved
       | _, _ ->
          begin
            match Substitution.add m (Mlty.Arrow (arg, out)) s with
            | Some s ->
               (), s, env.unsolved
            | None -> Mlty.error ~loc (Mlty.InvalidApplication (h, arg, out))
          end
     end

  | (Mlty.String | Mlty.Ref _ | Mlty.Dynamic _ | Mlty.Param _ | Mlty.Prod _
     |  Mlty.Handler _ | Mlty.App _) ->
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

  | (Mlty.Judgment | Mlty.String | Mlty.Ref _ | Mlty.Dynamic _ |  Mlty.Param _ |
     Mlty.Prod _ | Mlty.Arrow _ | Mlty.App _) ->
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

  | (Mlty.Judgment | Mlty.String | Mlty.Param _ | Mlty.Prod _ | Mlty.Handler _ |
     Mlty.Arrow _ | Mlty.App _ | Mlty.Dynamic _) ->
     Mlty.error ~loc (Mlty.RefExpected t)

let as_dynamic ~loc t env =
  let t = whnf env.context env.substitution t in
  match t with

  | Mlty.Dynamic t -> return t env

  | Mlty.Meta m ->
     let a = Mlty.fresh_type () in
     begin match Substitution.add m (Mlty.Dynamic a) env.substitution with
           | Some substitution -> return a {env with substitution}
           | None -> assert false
     end

  | (Mlty.Judgment | Mlty.String | Mlty.Param _ | Mlty.Prod _ | Mlty.Handler _ |
     Mlty.Arrow _ | Mlty.App _ | Mlty.Ref _) ->
     Mlty.error ~loc (Mlty.DynamicExpected t)

let op_cases op ~output m env =
  let argts, context = Context.op_cases op ~output env.context in
  m argts {env with context}

let at_toplevel env m =
  let x, substitution, unsolved = m env in
  { env with substitution; unsolved }, x

let predefined_type x ts env =
  let t = Context.predefined_type x ts env.context in
  return t env

let generalizes_to ~loc t (ps, u) env =
  let (), substitution, unsolved = add_equation ~loc t u env in
  (* NB: [s1] is the one that has [ps] appearing in the image *)
  let s1, s2 = Substitution.partition
            (fun _ t -> Mlty.params_occur ps t)
            substitution
  in
  let s1dom = Substitution.domain s1 in
  let known =
    Mlty.MetaSet.union
      (* XXX is it [substitution] or one of [s1], [s2]? *)
      (Context.gather_known s2 env.context)
      (unsolved_known unsolved)
  in
  let ms = Mlty.MetaSet.inter s1dom known in
  if Mlty.MetaSet.is_empty ms
  then
    (), s2, unsolved
  else
    let ps =
      List.filter
        (fun p ->
         Mlty.MetaSet.exists
           (fun m -> Mlty.params_occur [p] (Substitution.apply s1 (Mlty.Meta m)))
           ms)
        ps
    in
    Mlty.error ~loc (Mlty.Ungeneralizable (ps, u))

let normalize_schema (ps, t) env =
  let t = Substitution.apply env.substitution t in
  return (ps, t) env

(* Toplevel functionality *)

let topadd_tydef t d env =
  let context = Context.add_tydef t d env.context in
  { env with context }

let topadd_operation op opty env =
  let context = Context.add_operation op opty env.context in
  { env with context }

let topadd_let x s env = add_let x s (fun env -> env) env
