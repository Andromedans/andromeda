type t =
  { context : Context.t;
    substitution : Substitution.t;
    local_values : (Name.t * Mlty.ty) list (* the variables bound since the last call to [locally] *)
 }

type 'a tyenvM = t -> 'a * t

let empty =
  { context = Context.empty;
    substitution = Substitution.empty;
    local_values = []
  }

let return x env = x, env

let (>>=) m f env =
  let x, env = m env in
  f x env

let run env m = let x, env = m env in env, x

let get_context env = env.context, env

let gather_known ~known_context env =
  Mlty.MetaSet.union
    (Context.gather_known env.substitution known_context)
    (Substitution.domain env.substitution)

let remove_known ~known s =
  (* XXX: why isn't this just Mlty.MetaSet.diff s known ? *)
  Mlty.MetaSet.fold Mlty.MetaSet.remove known s

let generalize ~known_context t env =
  let known = gather_known ~known_context env in
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

let locally m env =
  let context = env.context in
  let x, env = m env in
  x, {env with context}

let record_ml_values m env =
  let local_values = env.local_values in
  let x, env = m {env with local_values = []} in
  (* XXX should we apply the substition to the types of local vars that we're returning? *)
  (List.rev env.local_values, x), {env with local_values}

let record_ml_value x t env =
  let t = Substitution.apply env.substitution t in
  (), {env with local_values = (x,t) :: env.local_values}

let add_ml_value x t env =
  let t = Substitution.apply env.substitution t in
  let context = Context.add_ml_value x ([], t) env.context in
  (), {env with context}

let locally_add_ml_value x t m =
  locally (add_ml_value x t >>= fun () -> m)

let add_ml_value x s env =
  let context = Context.add_ml_value x s env.context in
  (), {env with context}

let lookup_bound k env =
  let t = Context.lookup_bound k env.context in
  return t env

let lookup_ml_value v env =
  let t = Context.lookup_ml_value v env.context in
  return t env

let lookup_ml_operation op env =
  return (Context.lookup_ml_operation op env.context) env

let lookup_ml_constructor c env =
  return (Context.lookup_ml_constructor c env.context) env

let lookup_tt_constructor c env =
  return (Context.lookup_tt_constructor c env.context) env

let lookup_continuation env =
  return (Context.lookup_continuation env.context) env

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

  | (Mlty.Judgement _ | Mlty.String | Mlty.Param _ | Mlty.Prod _ | Mlty.Arrow _ |
     Mlty.Handler _ | Mlty.Ref _ | Mlty.Dynamic _) as t -> t

(** Unify types [t] and [t'] under current substitition [s],
    and return the updated substitution, or [None] if the types
    are not unifiable. *)
let rec unifiable ctx s t t' =
  let rec unifiable_judgement_abstraction s abstr1 abstr2 =
    match abstr1, abstr2 with
    | Mlty.NotAbstract frm1, Mlty.NotAbstract frm2 ->
       if frm1 = frm2 then
         Some s
       else
         None
    | Mlty.Abstract abstr1, Mlty.Abstract abstr2 ->
       unifiable_judgement_abstraction s abstr1 abstr2
    | Mlty.NotAbstract _, Mlty.Abstract _
    | Mlty.Abstract _, Mlty.NotAbstract _ -> None
  in
  let (>?=) m f = match m with
    | Some x -> f x
    | None -> None
  in
  match whnf ctx s t, whnf ctx s t' with
  | Mlty.Judgement abstr1, Mlty.Judgement abstr2 ->
     unifiable_judgement_abstraction s abstr1 abstr2

  | Mlty.String, Mlty.String ->
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

  | (Mlty.Judgement _ | Mlty.String | Mlty.Ref _ | Mlty.Dynamic _ | Mlty.Prod _ |
     Mlty.Param _ | Mlty.Arrow _ | Mlty.Handler _ | Mlty.Apply _), _ ->
     None

let add_tt_constructor c t env =
  let context = Context.add_tt_constructor c t env.context in
  (), {env with context}

let add_equation ~loc t t' env =
  match unifiable env.context env.substitution t t' with

  | Some s ->
     return () {env with substitution=s}

  | None ->
     Mlty.error ~loc
                (Mlty.TypeMismatch (Substitution.apply env.substitution t,
                                    Substitution.apply env.substitution t'))

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

  | (Mlty.Judgement _ | Mlty.String | Mlty.Ref _ | Mlty.Dynamic _ |  Mlty.Param _ |
     Mlty.Prod _ | Mlty.Arrow _ | Mlty.Apply _) ->
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

  | (Mlty.Judgement _ | Mlty.String | Mlty.Param _ | Mlty.Prod _ | Mlty.Handler _ |
     Mlty.Arrow _ | Mlty.Apply _ | Mlty.Dynamic _) ->
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

  | (Mlty.Judgement _ | Mlty.String | Mlty.Param _ | Mlty.Prod _ | Mlty.Handler _ |
     Mlty.Arrow _ | Mlty.Apply _ | Mlty.Ref _) ->
     Mlty.error ~loc (Mlty.DynamicExpected t)

let op_cases op ~output m env =
  let argts, context = Context.op_cases op ~output env.context in
  m argts {env with context}

let generalizes_to ~loc ~known_context t (ps, u) env =
  let (), env = add_equation ~loc t u env in
  (* NB: [s1] is the one that has [ps] appearing in the image *)
  let s1, s2 = Substitution.partition
            (fun _ t -> Mlty.params_occur ps t)
            env.substitution
  in
  let s1dom = Substitution.domain s1 in
  let known =
      (* XXX is it [substitution] or one of [s1], [s2]? *)
      Context.gather_known s2 known_context
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
    Mlty.error ~loc (Mlty.Ungeneralizable (ps, u))

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

let print_context {context;_} = Context.print_context context
