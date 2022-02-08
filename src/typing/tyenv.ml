type t =
  { context : Context.t;
    substitution : Substitution.t;
  }

type judgement_or_boundary =
  | Is_judgement
  | Is_boundary

type derivation_or_function =
  | Is_derivation
  | Is_function of Mlty.ty * Mlty.ty

type 'a tyenvM = t -> 'a * t

let empty =
  { context = Context.empty;
    substitution = Substitution.empty
  }

let return x env = x, env

let (>>=) m f env =
  let x, env = m env in
  f x env

let run env m = let x, env = m env in env, x

let gather_known env =
  Mlty.MetaSet.union
    (Context.gather_known env.substitution env.context)
    (Substitution.domain env.substitution)

let remove_known ~known s =
  (* XXX: why isn't this just Mlty.MetaSet.diff s known ? *)
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

let ungeneralize t env =
  let t = Substitution.apply env.substitution t in
  return ([], t) env

let add_bound_mono x t m env =
  let t = Substitution.apply env.substitution t in
  let context = Context.add_bound x ([], t) env.context in
  let r, {substitution;context=_} = m { env with context } in
  r, { env with substitution }

let rec add_bounds_mono xts m env =
  match xts with
  | [] -> m env
  | (x,t) :: xts ->
     add_bound_mono x t (add_bounds_mono xts m) env

let add_bound_poly x s m env =
  (* XXX should we apply the subtitition, like in [add_bound_mono]? *)
  let context = Context.add_bound x s env.context in
  let r, {substitution;context=_} = m { env with context } in
  r, { env with substitution }

let rec add_bounds_poly xss m env =
  match xss with
  | [] -> m env
  | (x,s) :: xss ->
     add_bound_poly x s (add_bounds_poly xss m) env

let add_ml_value_mono x t m env =
  let t = Substitution.apply env.substitution t in
  let context = Context.add_ml_value x ([], t) env.context in
  m {env with context}

let add_ml_value_poly x s m env =
  (* XXX should we apply the subtitition, like in [add_ml_value_mono]? *)
  let context = Context.add_ml_value x s env.context in
  m {env with context}

let rec add_ml_values_poly xss m env =
  match xss with
  | [] -> m env
  | (x,s) :: xss ->
     add_ml_value_poly x s (add_ml_values_poly xss m) env

let as_module m env =
  let context = Context.push_ml_module env.context in
  let x, env = m { env with context } in
  let context = Context.pop_ml_module env.context in
  x, { env with context }

let lookup_bound k env =
  let t = Context.lookup_bound k env.context in
  return t env

let lookup_ml_value v env =
  let t = Context.lookup_ml_value v env.context in
  return t env

let lookup_ml_operation op env =
  return (Context.lookup_ml_operation op env.context) env

let lookup_ml_exception exc env =
  return (Context.lookup_ml_exception exc env.context) env

let lookup_ml_constructor c env =
  return (Context.lookup_ml_constructor c env.context) env

let lookup_tt_constructor c env =
  return (Context.lookup_tt_constructor c env.context) env


(* Whnf for meta instantiations and type aliases *)
let rec whnf ctx s = function

  | Mlty.Meta m as t ->
     begin match Substitution.lookup m s with
           | Some t -> whnf ctx s t
           | None -> t
     end

  | Mlty.Apply (head, ts) as t ->
     begin match Context.unfold ctx head ts with
     | Some t -> whnf ctx s t
     | None -> t
     end

  | Mlty.(Judgement | Boundary | Derivation | Transformation | String | Param _ | Prod _ | Arrow _ |
     Handler _ | Ref _ | Exn) as t -> t

(** Unify types [t] and [t'] under current substitition [s],
    and return the updated substitution, or [None] if the types
    are not unifiable. *)
let rec unifiable ctx s t t' =
  let (>?=) m f = match m with
    | Some x -> f x
    | None -> None
  in
  match whnf ctx s t, whnf ctx s t' with
  | Mlty.(Judgement, Judgement)
  | Mlty.(Boundary, Boundary)
  | Mlty.(Derivation, Derivation)
  | Mlty.(Transformation, Transformation)
  | Mlty.(String, String)
  | Mlty.(Exn, Exn) ->
     Some s

  | Mlty.Meta m, Mlty.Meta m' when Mlty.eq_meta m m' ->
     Some s

  | Mlty.Meta m, t ->
     Substitution.add m t s

  | t, Mlty.Meta m ->
     Substitution.add m t s

  | Mlty.Param p, Mlty.Param p' when Mlty.eq_param p p' ->
     Some s

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

  | Mlty.Apply (x_pth, ts), Mlty.Apply (y_pth, ts') ->
     let x_id = Context.lookup_ml_type_id x_pth ctx in
     let y_id = Context.lookup_ml_type_id y_pth ctx in
     begin match Ident.equal x_id y_id with
     | false -> None
     | true ->
        let rec fold s ts ts' = match ts, ts' with
          | [], [] -> Some s
          | t :: ts, t' :: ts' ->
             unifiable ctx s t t' >?= fun s ->
                                      fold s ts ts'
          | [], _ :: _ | _ :: _, [] -> assert false
        in
        fold s ts ts'
     end

  | Mlty.(Judgement | Boundary | Derivation | Transformation | String | Ref _ | Exn | Prod _ |
     Param _ | Arrow _ | Handler _ | Apply _), _ ->
     None

let add_tt_constructor c env =
  let context = Context.add_tt_constructor c env.context in
  (), {env with context}

let add_equation ~at t t' env =
  match unifiable env.context env.substitution t t' with

  | Some s ->
     return () {env with substitution=s}

  | None ->
     Mlty.(error ~at
                (TypeMismatch (Substitution.apply env.substitution t,
                               Substitution.apply env.substitution t')))

let as_judgement_or_boundary ~at t env =
  let t = whnf env.context env.substitution t in
  match t with

  | Mlty.Judgement -> return Is_judgement env

  | Mlty.Boundary -> return Is_boundary env

  | Mlty.Meta _ ->
     Mlty.error ~at Mlty.UninferrableExpression

  | Mlty.(Derivation | Transformation | String | Ref _ | Exn |  Param _ | Handler _ | Prod _ | Arrow _ | Apply _) ->
     Mlty.(error ~at (JudgementOrBoundaryExpected t))

let as_derivation_or_function ~at t env =
  let t = whnf env.context env.substitution t in
  match t with

  | Mlty.Derivation -> return Is_derivation env

  | Mlty.Arrow (t, u) -> return (Is_function (t, u)) env

  | Mlty.Meta _ as t ->
     let t1 = Mlty.fresh_type ()
     and t2 = Mlty.fresh_type () in
     (add_equation ~at t (Mlty.Arrow (t1, t2)) >>= fun () -> return (Is_function (t1, t2))) env

  | Mlty.(Judgement | Boundary | Transformation | String | Ref _ | Exn | Param _ | Handler _ | Prod _ | Apply _) ->
     Mlty.(error ~at (DerivationOrFunctionExpected t))

let as_handler ~at t env =
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

  | Mlty.(Judgement | Boundary | Derivation | Transformation | String | Ref _ | Exn |  Param _ |
     Prod _ | Arrow _ | Apply _) ->
     Mlty.(error ~at (HandlerExpected t))

let as_ref ~at t env =
  let t = whnf env.context env.substitution t in
  match t with

  | Mlty.Ref t -> return t env

  | Mlty.Meta m ->
     let a = Mlty.fresh_type () in
     begin match Substitution.add m (Mlty.Ref a) env.substitution with
           | Some substitution -> return a {env with substitution}
           | None -> assert false
     end

  | Mlty.(Judgement | Boundary | Derivation | Transformation | String | Param _ | Prod _ | Handler _ |
     Arrow _ | Apply _ | Exn) ->
     Mlty.(error ~at (RefExpected t))


let generalizes_to ~at t (ps, u) env =
  let (), env = add_equation ~at t u env in
  (* NB: [s1] is the one that has [ps] appearing in the image *)
  let s1, s2 = Substitution.partition
            (fun _ t -> Mlty.params_occur ps t)
            env.substitution
  in
  let s1dom = Substitution.domain s1 in
  let known =
      (* XXX is it [substitution] or one of [s1], [s2]? *)
      Context.gather_known s2 env.context
  in
  let ms = Mlty.MetaSet.inter s1dom known in
  if Mlty.MetaSet.is_empty ms
  then
    (), {env with substitution=s2}
  else
    let ps =
      List.filter
        (fun p ->
         Mlty.MetaSet.exists
           (fun m -> Mlty.params_occur [p] (Substitution.apply s1 (Mlty.Meta m)))
           ms)
        ps
    in
    Mlty.error ~at (Mlty.Ungeneralizable (ps, u))

(* let normalize_schema (ps, t) env = *)
(*   let t = Substitution.apply env.substitution t in *)
(*   return (ps, t) env *)

(* Toplevel functionality *)

let add_ml_type t d env =
  let context = Context.add_ml_type t d env.context in
  (), { env with context }

let add_ml_operation op opty env =
  let context = Context.add_ml_operation op opty env.context in
  (), { env with context }

let add_ml_exception exc opty env =
  let context = Context.add_ml_exception exc opty env.context in
  (), { env with context }
