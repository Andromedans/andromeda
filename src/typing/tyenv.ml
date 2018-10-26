(* Application is over-loaded, as [e1 e2] could mean that we're applying an AML
   function [e1] to an AML arguement [e2], or that we're applying a judgement
   [e1] to a judgement [e2]. If [e1 : t1], [e2 : t2] and [e1 e2 : t3] then
   [AppConstraint (_, t1, t2, t3)] represents the contraint that applying
   something of type [t1] to something of type [t2] gives something of type
   [t3]. *)
type constrain =
  | AppConstraint of Location.t * Mlty.ty * Mlty.ty * Mlty.ty

type t =
  { context : Context.t;
    substitution : Substitution.t;
    unsolved : constrain list;
    local_vars : (Name.ident * Mlty.ty) list (* the variables bound since the last call to [locally] *)
 }

type 'a tyenvM = t -> 'a * t

let empty =
  { context = Context.empty;
    substitution = Substitution.empty;
    unsolved = [];
    local_vars = []
  }

let return x env = x, env

let (>>=) m f env =
  let x, env = m env in
  f x env

let run env m = let x, env = m env in env, x

let get_context env = env.context, env

let unsolved_known unsolved =
  List.fold_left
    (fun known (AppConstraint (_, t1, t2, t3)) ->
      Mlty.MetaSet.union known
                         (Mlty.MetaSet.union
                            (Mlty.occuring t1)
                            (Mlty.MetaSet.union (Mlty.occuring t2) (Mlty.occuring t3))))
    Mlty.MetaSet.empty unsolved

let gather_known ~known_context env =
  Mlty.MetaSet.union
    (Mlty.MetaSet.union
       (Context.gather_known env.substitution known_context)
       (Substitution.domain env.substitution))
    (unsolved_known env.unsolved)

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

let record_vars m env =
  let local_vars = env.local_vars in
  let x, env = m {env with local_vars = []} in
  (* XXX should we apply the substition to the types of local vars that we're returning? *)
  (List.rev env.local_vars, x), {env with local_vars}

let record_var x t env =
  let t = Substitution.apply env.substitution t in
  (), {env with local_vars = (x,t) :: env.local_vars}

let add_var x t env =
  let t = Substitution.apply env.substitution t in
  let context = Context.add_let x ([], t) env.context in
  (), {env with context}

let locally_add_var x t m =
  locally (add_var x t >>= fun () -> m)

let add_let x s env =
  let context = Context.add_let x s env.context in
  (), {env with context}

let lookup_var k env =
  let t = Context.lookup_var k env.context in
  return t env

let lookup_op op env =
  return (Context.lookup_op op env.context) env

let lookup_aml_constructor c env =
  return (Context.lookup_aml_constructor c env.context) env

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

  | Mlty.App (_, x, ts) as t ->
     begin match Context.unfold ctx x ts with
           | Some t -> whnf ctx s t
           | None -> t
     end

  | (Mlty.Judgement _ | Mlty.String | Mlty.Param _ | Mlty.Prod _ | Mlty.Arrow _ |
     Mlty.Handler _ | Mlty.Ref _ | Mlty.Dynamic _) as t -> t

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

  | (Mlty.Judgement _ | Mlty.String | Mlty.Ref _ | Mlty.Dynamic _ | Mlty.Prod _ |
     Mlty.Param _ | Mlty.Arrow _ | Mlty.Handler _ | Mlty.App _), _ ->
     None

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

(* XXX this is severely broken at the moment, as it will allow application of
   one [is_term] judgement to another. We need to deal with this in the future. *)
and add_application ~loc h arg out env =
  let s = env.substitution in
  let h = whnf env.context s h
  and arg = whnf env.context s arg
  and out = whnf env.context s out in
  match h with

  | Mlty.Judgement (Mlty.NotAbstract Mlty.IsTerm) as t->
     (>>=) (add_equation ~loc arg t) (fun () -> add_equation ~loc out t) env

  | Mlty.Arrow (a, b) ->
     (>>=) (add_equation ~loc arg a) (fun () -> add_equation ~loc out b) env

  | Mlty.Meta m ->
     begin
       match arg, out with
       | (Mlty.Judgement (Mlty.NotAbstract Mlty.IsTerm) | Mlty.Meta _),
         (Mlty.Judgement (Mlty.NotAbstract Mlty.IsTerm) | Mlty.Meta _) ->
          let unsolved = AppConstraint (loc, h, arg, out) :: env.unsolved in
          (), { env with unsolved }
       | _, _ ->
          begin
            match Substitution.add m (Mlty.Arrow (arg, out)) s with
            | Some substitution ->
               (), { env with substitution }
            | None -> Mlty.error ~loc (Mlty.InvalidApplication (h, arg, out))
          end
     end

  | (Mlty.Judgement _ | Mlty.String | Mlty.Ref _ | Mlty.Dynamic _ | Mlty.Param _ |
     Mlty.Prod _ |  Mlty.Handler _ | Mlty.App _) ->
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

  | (Mlty.Judgement _ | Mlty.String | Mlty.Ref _ | Mlty.Dynamic _ |  Mlty.Param _ |
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

  | (Mlty.Judgement _ | Mlty.String | Mlty.Param _ | Mlty.Prod _ | Mlty.Handler _ |
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

  | (Mlty.Judgement _ | Mlty.String | Mlty.Param _ | Mlty.Prod _ | Mlty.Handler _ |
     Mlty.Arrow _ | Mlty.App _ | Mlty.Ref _) ->
     Mlty.error ~loc (Mlty.DynamicExpected t)

let op_cases op ~output m env =
  let argts, context = Context.op_cases op ~output env.context in
  m argts {env with context}

let predefined_type x ts env =
  let t = Context.predefined_type x ts env.context in
  return t env

let generalizes_to ~loc ~known_context t (ps, u) env =
  let (), env = add_equation ~loc t u env in
  (* NB: [s1] is the one that has [ps] appearing in the image *)
  let s1, s2 = Substitution.partition
            (fun _ t -> Mlty.params_occur ps t)
            env.substitution
  in
  let s1dom = Substitution.domain s1 in
  let known =
    Mlty.MetaSet.union
      (* XXX is it [substitution] or one of [s1], [s2]? *)
      (Context.gather_known s2 known_context)
      (unsolved_known env.unsolved)
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

let add_tydef t d env =
  let context = Context.add_tydef t d env.context in
  (), { env with context }

let add_operation op opty env =
  let context = Context.add_operation op opty env.context in
  (), { env with context }

let print_context {context;_} = Context.print_context context
