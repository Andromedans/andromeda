open Amltype

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
    MetaSet.union (Context.gather_known env.topctx) (Substitution.gather_known env.topsubst)

  let add_lets xts env =
    let known = gather_known env in
    let topctx = Context.add_lets xts known env.topsubst env.topctx in
    {env with topctx}
end

module Env : sig
  type 'a mon

  val return : 'a -> 'a mon

  val (>>=) : 'a mon -> ('a -> 'b mon) -> 'b mon

  val at_toplevel : TopEnv.t -> 'a mon -> 'a * TopEnv.t

  val lookup_var : Syntax.bound -> ty mon

  val lookup_op : Name.operation -> (ty list * ty) mon

  val lookup_constructor : Name.constructor -> (ty list * ty) mon

  val lookup_continuation : (ty * ty) mon

  val add_var : Name.ident -> ty -> 'a mon -> 'a mon

  val add_equation : loc:Location.t -> ty -> ty -> unit mon

  val add_application : loc:Location.t -> ty -> ty -> ty -> unit mon

  val add_lets : (Name.ident * Context.generalizable * ty) list -> 'a mon -> 'a mon

  val as_handler : loc:Location.t -> ty -> (ty * ty) mon

  val as_ref : loc:Location.t -> ty -> ty mon

  val op_cases : Name.operation -> output:ty -> (ty list -> 'a mon) -> 'a mon
end = struct
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
    let context = Context.add_var x (ungeneralized_schema t) env.context in
    m {env with context}

  let gather_known env =
    let known = MetaSet.union (Context.gather_known env.context) (Substitution.gather_known env.substitution) in
    List.fold_left (fun known (Context.AppConstraint (_, t1, t2, t3)) ->
        MetaSet.union known (MetaSet.union (occuring t1) (MetaSet.union (occuring t2) (occuring t3))))
      known env.unsolved

  let add_lets xts m env =
    let known = gather_known env in
    let context = Context.add_lets xts known env.substitution env.context in
    m {env with context}

  (* Whnf for meta instantiations and type aliases *)
  let rec whnf ctx s = function
    | Meta m as t ->
      begin match Substitution.lookup m s with
        | Some t -> whnf ctx s t
        | None -> t
      end
    | App (_, x, ts) as t ->
      begin match Context.unfold ctx x ts with
        | Some t -> whnf ctx s t
        | None -> t
      end
    | _ as t -> t

  let rec unifiable ctx s t t' =
    let (>?=) m f = match m with
      | Some x -> f x
      | None -> None
    in
    match whnf ctx s t, whnf ctx s t' with
      | Jdg, Jdg | String, String -> Some s
      | Meta m, Meta m' when m = m' -> Some s
      | Meta m, t -> Substitution.add m t s
      | t, Meta m -> Substitution.add m t s
      | Ref t, Ref t' -> unifiable ctx s t t'
      | Tuple ts, Tuple ts' ->
        let rec fold s ts ts' = match ts, ts' with
          | [], [] -> Some s
          | t :: ts, t' :: ts' ->
            unifiable ctx s t t' >?= fun s ->
            fold s ts ts'
          | [], _ :: _ | _ :: _, [] -> None
        in
        fold s ts ts'
      | Arrow (t1, t2), Arrow (t1', t2') ->
        unifiable ctx s t1 t1' >?= fun s ->
        unifiable ctx s t2 t2'
      | Handler (t1, t2), Handler (t1', t2') ->
        unifiable ctx s t1 t1' >?= fun s ->
        unifiable ctx s t2 t2'
      | App (_, x, ts), App (_, y, ts') when x = y ->
        let rec fold s ts ts' = match ts, ts' with
          | [], [] -> Some s
          | t :: ts, t' :: ts' ->
            unifiable ctx s t t' >?= fun s ->
            fold s ts ts'
          | [], _ :: _ | _ :: _, [] -> assert false
        in
        fold s ts ts'
      | (Jdg | String | Ref _ | Tuple _ | Arrow _ | Handler _ | App _), _ -> None

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
      | None -> error ~loc (TypeMismatch (Substitution.apply env.substitution t,
                                          Substitution.apply env.substitution t'))

  and add_application ~loc h arg out env =
    let s = env.substitution in
    let h = whnf env.context s h
    and arg = whnf env.context s arg
    and out = whnf env.context s out in
    match h, arg, out with
      | Jdg, _, _ ->
        (>>=) (add_equation ~loc arg Jdg) (fun () -> add_equation ~loc out Jdg) env
      | Arrow (a, b), _, _ ->
        (>>=) (add_equation ~loc arg a) (fun () -> add_equation ~loc out b) env
      | Meta _, (Jdg | Meta _), (Jdg | Meta _) ->
        let unsolved = Context.AppConstraint (loc, h, arg, out) :: env.unsolved in
        (), s, unsolved
      | Meta m, _, _ ->
        begin match Substitution.add m (Arrow (arg, out)) s with
          | Some s ->
            (), s, env.unsolved
          | None -> error ~loc (InvalidApplication (h, arg, out))
        end
      | _, _, _ -> error ~loc (InvalidApplication (h, arg, out))

  let as_handler ~loc t env =
    let t = whnf env.context env.substitution t in
    match t with
      | Handler (a, b) -> return (a, b) env
      | Meta m ->
        let a = fresh_type ()
        and b = fresh_type () in
        begin match Substitution.add m (Handler (a, b)) env.substitution with
          | Some substitution -> return (a, b) {env with substitution}
          | None -> assert false
        end
      | _ -> error ~loc (HandlerExpected t)

  let as_ref ~loc t env =
    let t = whnf env.context env.substitution t in
    match t with
      | Ref t -> return t env
      | Meta m ->
        let a = fresh_type () in
        begin match Substitution.add m (Ref a) env.substitution with
          | Some substitution -> return a {env with substitution}
          | None -> assert false
        end
      | _ -> error ~loc (RefExpected t)

  let op_cases op ~output m env =
    let argts, context = Context.op_cases op ~output env.context in
    m argts {env with context}

  let to_solved env =
    match env.unsolved with
      | [] -> {TopEnv.topctx = env.context; topsubst = env.substitution}
      | Context.AppConstraint (loc, arg, h, out) :: unsolved ->
        let s = env.substitution in
        let h = Substitution.apply s h
        and arg = Substitution.apply s arg
        and out = Substitution.apply s out in
        error ~loc (UnsolvedApp (arg, h, out))

  let at_toplevel top m =
    let env = of_topenv top in
    let x, substitution, unsolved = m env in
    let top = to_solved {env with substitution; unsolved} in
    x, top
end

