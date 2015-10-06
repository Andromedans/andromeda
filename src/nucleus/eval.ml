(** Evaluation of computations *)

(** Auxiliary printing functions. *)

let print_term env e =
    let xs = Environment.used_names env in
      Tt.print_term xs e

let print_ty env t =
    let xs = Environment.used_names env in
      Tt.print_ty xs t

(** Notation for the monadic bind *)
let (>>=) = Value.bind

(** A filter that verifies the result is a term. *)
let as_term ~loc v =
  let e = Value.as_term ~loc v in
    Value.return e

(** A filter that verifies the result is a type. *)
let as_ty ~loc v =
  let t = Value.as_ty ~loc v in
    Value.return t

(** Evaluation of expressions. *)
let rec expr env (e',loc) =
  let close x c v =
    let env = Environment.add_bound x v env in
    infer env c
  in
  begin
    match e' with

    | Syntax.Bound i -> Environment.lookup_bound i env

    | Syntax.Type ->
       let e = Tt.mk_type ~loc in
       let t = Tt.mk_type_ty ~loc in
       let et = Judgement.mk_term Context.empty e t in
       Value.Term et

    | Syntax.Function (x, c) ->
       Value.Closure (close x c)

    | Syntax.Handler {Syntax.handler_val; handler_ops; handler_finally} ->
       let handler_val =
         begin match handler_val with
         | None -> None
         | Some (x, c) -> Some (close x c)
         end
       and handler_ops =
         begin
           let close2 x1 x2 c v1 v2 =
             let env = Environment.add_bound x1 v1 env in
             let env = Environment.add_bound x2 v2 env in
             infer env c
           in
           List.map (fun (op, (x, k, c)) -> (op, close2 x k c)) handler_ops
         end
       and handler_finally =
         begin match handler_finally with
         | None -> None
         | Some (x, c) -> Some (close x c)
         end
       in
       Value.Handler (Value.{handler_val; handler_ops; handler_finally})
  end

and expr_term env ((_,loc) as e) =
  match expr env e with
  (* | Value.Ty (Tt.Ty t) -> Judgement.mk_term t Tt.typ *)
  | Value.Ty _ -> Error.runtime ~loc "this expression should be a term but is a type"
  | Value.Term et -> et
  | Value.Handler _ -> Error.runtime ~loc "this expression should be a term but is a handler"
  | Value.Closure _ -> Error.runtime ~loc "this expression should be a term but is a handler"

(** Evaluate a computation -- infer mode. *)
and infer env (c',loc) =
  match c' with

  | Syntax.Return e ->
     let v = expr env e in
     Value.Return v

  | Syntax.Operation (op, e) ->
     let v = expr env e in
     let k u = Value.Return u in
     Value.Operation (op, v, k)

  | Syntax.With (e, c) ->
     let h = Value.as_handler ~loc:(snd e) (expr env e) in
     let r = infer env c in
     handle_result env h r

  | Syntax.Let (xcs, c) ->
     let_bind env xcs >>= (fun env -> infer env c)

  | Syntax.Apply (e1, e2) ->
     let v1 = Value.as_closure ~loc (expr env e1)
     and v2 = expr env e2 in
       v1 v2

  | Syntax.Beta (xscs, c) ->
    beta_bind env xscs >>= (fun env -> infer env c)

  | Syntax.Eta (xscs, c) ->
    eta_bind env xscs >>= (fun env -> infer env c)

  | Syntax.Hint (xscs, c) ->
    hint_bind env xscs >>= (fun env -> infer env c)

  | Syntax.Inhabit (xscs, c) ->
    inhabit_bind env xscs >>= (fun env -> infer env c)

  | Syntax.Unhint (xs, c) ->
    let env = Environment.unhint xs env in
    infer env c

  | Syntax.Whnf c ->
    infer env c >>= as_term ~loc >>=
    (fun (ctx, e, t) ->
      let e = Equal.whnf env e
      and t = Equal.whnf_ty env t in
      let j = Judgement.mk_term ctx e t in
      Value.return_term j)

  | Syntax.Typeof c ->
    (* In future versions this is going to be a far less trivial computation,
       as it might actually fail when there is no way to name a type with a term. *)
    infer env c >>= as_term ~loc >>=
    (fun (ctx, _, Tt.Ty t) ->
     let j = Judgement.mk_term ctx t Tt.typ in
         Value.return_term j)

  | Syntax.Ascribe (c1, c2) ->
     check_ty env c2 >>=
       (fun ((ctxt, t') as t) ->
        check env c1 t >>=
          (fun (ctxe, e) ->
           let ctx, eqs = Context.join ctxe ctxt in
           (* XXX do something with equations *)
           let j = Judgement.mk_term ctx e t' in
           Value.return_term j))

  | Syntax.Constant (x, cs) ->
     failwith "eval.ml not implemented Syntax.Constant"
(*
    let yts, u =
      begin match Environment.lookup_constant x env with
      | Some ytsu -> ytsu
      | None -> Error.typing "unknown constant %t" (Name.print_ident x)
      end in
    let rec fold es yts cs =
      match yts, cs with
      | [], [] ->
        let u = Tt.instantiate_ty es 0 u
        and e = Tt.mk_constant ~loc x (List.rev es) in
        let eu = Judgement.mk_term e u in
        Value.return_term eu

      | (y,(reducing,t))::yts, c::cs ->
        let t = Tt.instantiate_ty es 0 t in
        check env c t >>= as_term ~loc >>=
          (fun e _ ->
           let e = if reducing then Equal.whnf env e else e in
             fold (e :: es) yts cs)

      | _::_, [] ->
        Error.typing ~loc "too few arguments in a primitive operation (%d missing)"
          (List.length yts)

      | _, _::_ ->
        Error.typing ~loc "too many arguments in a primitive operation (%d extra)"
          (List.length cs)
    in
    fold [] yts cs
 *)

  | Syntax.Lambda (xus, c) ->
     infer_lambda env ~loc xus c >>=
       (fun (ctx, lam, prod) -> Value.return_term (Judgement.mk_term ctx lam prod))

  | Syntax.Spine (e, []) ->
      Value.return_term (expr_term env e)

  | Syntax.Spine (e, cs) ->
    let j = expr_term env e in
    spine ~loc env j cs

  | Syntax.Prod (xts, c) ->
    infer_prod env ~loc xts c

  | Syntax.Eq (c1, c2) ->
     infer env c1 >>= as_term ~loc:(snd c1) >>=
       (fun (ctx1, e1, t1') ->
        let t1 = Judgement.mk_ty ctx1 t1' in
        check env c2 t1 >>=
          (fun (ctx2, e2) ->
           let eq = Tt.mk_eq ~loc t1' e1 e2 in
           let typ = Tt.mk_type_ty ~loc in
           let ctx, eqs = Context.join ctx1 ctx2 in
           (* XXX do something about equations *)
           let j = Judgement.mk_term ctx eq typ in
           Value.return_term j))

  | Syntax.Refl c ->
     infer env c >>= as_term ~loc:(snd c) >>=
       (fun (ctxe, e, t) ->
        let e' = Tt.mk_refl ~loc t e
        and t' = Tt.mk_eq_ty ~loc t e e in
        let et' = Judgement.mk_term ctxe e' t' in
        Value.return_term et')

  | Syntax.Bracket c ->
    check_ty env c >>=
      (fun (ctxt, t') ->
       let t' = Tt.mk_bracket ~loc t' in
       let typ = Tt.mk_type_ty ~loc in
       let j = Judgement.mk_term ctxt t' typ in
       Value.return_term j)

  | Syntax.Inhab ->
    Error.typing ~loc "cannot infer the type of []"

and check env ((c',loc) as c) (((ctx_check, t_check') as t_check) : Judgement.ty) : (Context.t * Tt.term) Value.result =
  match c' with

  | Syntax.Return _
  | Syntax.With _
  | Syntax.Typeof _
  | Syntax.Apply _
  | Syntax.Constant _
  | Syntax.Prod _
  | Syntax.Eq _
  | Syntax.Spine _
  | Syntax.Bracket _  ->
    (** this is the [check-infer] rule, which applies for all term formers "foo"
        that don't have a "check-foo" rule *)

    infer env c >>= as_term ~loc >>=
      (fun (ctxe, e, t') ->
       let ctx, eqs = Context.join ctx_check ctxe in
       if Equal.equal_ty env t_check' t'
       then Value.return (ctx, e)
       else Error.typing ~loc:(snd e)
                         "this expression should have type@ %t@ but has type@ %t"
                         (print_ty env t_check') (print_ty env t'))

  | Syntax.Operation (op, e) ->
     let ve = expr env e
     and k v =
       let (ctxe, e', t') = Value.as_term ~loc v in
       let ctx, eqs = Context.join ctx_check ctxe in
       if Equal.equal_ty env t_check' t'
       then Value.return (ctx, e')
       else Error.typing ~loc:(snd e')
                         "this expression should have type@ %t@ but has type@ %t"
                         (print_ty env t_check') (print_ty env t')
     in
       Value.Operation (op, ve, k)

  | Syntax.Let (xcs, c) ->
     let_bind env xcs >>= (fun env -> check env c t_check)

  | Syntax.Beta (xscs, c) ->
     beta_bind env xscs >>= (fun env -> check env c t_check)

  | Syntax.Eta (xscs, c) ->
    eta_bind env xscs >>= (fun env -> check env c t_check)

  | Syntax.Hint (xscs, c) ->
    hint_bind env xscs >>= (fun env -> check env c t_check)

  | Syntax.Inhabit (xscs, c) ->
    inhabit_bind env xscs >>= (fun env -> check env c t_check)

  | Syntax.Unhint (xs, c) ->
    let env = Environment.unhint xs env in
    check env c t_check

  | Syntax.Whnf c ->
    check env c t_check >>=
    (fun (ctxe, e) ->
       let e = Equal.whnf env e in
       (* XXX in the future whnf will also return its own context that has to be joined here. *)
       Value.return (ctxe, e))

  | Syntax.Ascribe (c1, c2) ->
     check_ty env c2 >>=
       (fun ((ctxt, t') as t) ->
        let ctx, eqs = Context.join ctx_check ctxt in
        if Equal.equal_ty env t' t_check'
        then
          check env c1 t >>=
            (fun (ctx1, e1) ->
             let ctx, eqs = Context.join ctx ctx1 in
             Value.return (ctx, e1)
            )
        else
          Error.typing ~loc:(snd c2)
            "this type should be equal to@ %t" (print_ty env t_check'))

  | Syntax.Lambda (abs, c) ->
    check_lambda env ~loc t_check abs c

  | Syntax.Refl c ->
    let (t', e1, e2) = Equal.as_eq env t_check' in
    let t = Judgement.mk_ty ctx_check t' in
    check env c t >>=
      (fun (ctxe, e) ->
       let ctx, eqs = Context.join ctx_check ctxe in
       if Equal.equal env e e1 t'
       then if Equal.equal env e e2 t'
            then Value.return (ctx, Tt.mk_refl ~loc t' e)
            else Error.typing ~loc
                   "failed to check that the term@ %t is equal to@ %t"
                   (print_term env e) (print_term env e2)
       else Error.typing ~loc
              "failed to check that the term@ %t is equal to@ %t"
              (print_term env e) (print_term env e1))

  | Syntax.Inhab ->
    begin match Equal.as_bracket env t_check' with
      | Some t' ->
        begin match Equal.inhabit_bracket ~subgoals:true ~loc env t' with
          | Some _ -> Value.return (ctx_check, Tt.mk_inhab ~loc)
          | None -> Error.typing ~loc "do not know how to inhabit %t"
                      (print_ty env t')
        end
      | None -> Error.typing ~loc "[] has a bracket type and not %t"
                  (print_ty env t_check')
    end

and handle_result env {Value.handler_val; handler_ops; handler_finally} r =
  begin match r with
  | Value.Return v ->
     begin match handler_val with
     | Some f -> f v
     | None -> r
     end
  | Value.Operation (op, ve, cont) ->
     let h = Value.{handler_val; handler_ops; handler_finally=None} in
     let wrap cont v = handle_result env h (cont v) in
     begin
       try
         let f = List.assoc op handler_ops in
         f ve (Value.Closure (wrap cont))
       with
         Not_found ->
          Value.Operation (op, ve, (wrap cont))
     end
  end >>=
  (fun v ->
     match handler_finally with
     | Some f -> f v
     | None -> Value.Return v)

and infer_lambda env ~loc xus c =
  let rec fold env ctx zs xws  = function
      | [] ->
         infer env c >>= as_term ~loc:(snd c) >>=
           (fun (ctxe, e, t') ->
            let e = Tt.abstract zs 0 e in
            let t' = Tt.abstract_ty zs 0 t' in
            let ctx, eqs = Context.join ctx ctxe in
            (** XXX verify equations eqs *)
            let ctx = Context.abstract ctx zs in
            let xws = List.rev xws in
            let lam = Tt.mk_lambda ~loc xws e t' in
            let prod = Tt.mk_prod_ty ~loc xws t' in
            Value.return (ctx, lam, prod))
      | (x, None) :: _ ->
         Error.runtime ~loc "cannot infer the type of %t" (Name.print_ident x)
      | (x, Some c) :: xus ->
         check_ty env c >>=
           (fun ((ctxu, u') as u) ->
            (* XXX equip x with location and use for [~loc]. *)
            let z, env = Environment.add_fresh ~loc:Location.unknown env x u in
            let w' = Tt.abstract_ty zs 0 u' in
            let ctx, eqs = Context.join ctx ctxu in
            (** XXX verify equations eqs *)
            fold env ctx (z :: zs) ((x, w') :: xws) xus)
  in
  fold env Context.empty [] [] xus

and infer_prod env ~loc xus c =
  let rec fold env ctx zs xws  = function
      | [] ->
         check_ty env c >>=
           (fun (ctxt, t') ->
            let t' = Tt.abstract_ty zs 0 t' in
            let ctx, eqs = Context.join ctx ctxt in
            (** XXX verify equations eqs *)
            let ctx = Context.abstract ctx zs in
            let xws = List.rev xws in
            let prod = Tt.mk_prod ~loc xws t' in
            let typ = Tt.mk_type_ty ~loc in
            let j = Judgement.mk_term ctx prod typ in
            Value.return_term j)
      | (x, c) :: xus ->
         check_ty env c >>=
           (fun ((ctxu, u') as u) ->
            (* XXX equip x with location and use for [~loc]. *)
            let z, env = Environment.add_fresh ~loc:Location.unknown env x u in
            let w' = Tt.abstract_ty zs 0 u' in
            let ctx, eqs = Context.join ctx ctxu in
            (** XXX verify equations eqs *)
            fold env ctx (z :: zs) ((x, w') :: xws) xus)
  in
  fold env Context.empty [] [] xus


and check_lambda env ~loc ((ctx_check, t_check') as t_check) abs body : (Context.t * Tt.term) Value.result =
  (* If the abstractions are fully annotated with types then we
     infer the type of the lambda and compare it to [t],
     otherwise we express [t] as a product and descend into
     the abstraction. *)

  let all_tagged = List.for_all (function (_, None) -> false | (_, Some _) -> true) abs in

  if all_tagged then
    begin
     (* try to infer and check equality. this might not be the end of the
       story, [as_*] could be operations *)
     (* for instance, an alternative would be to make a fresh pi-type and check
       whether the type at hand [t] is equal to the fresh pi by a general hint,
       and then continue with that one *)

     (* XXX this generalisation should be done also in [fold] below and in
        [spine], same for other [as_*] functions  *)

      infer_lambda env ~loc abs body >>=
        (fun (ctxe, e, t') ->
         let ctx, eqs = Context.join ctx_check ctxe in
         if Equal.equal_ty env t_check' t'
         then Value.return (ctx, e)
         else Error.typing ~loc
               "this expression is an abstraction but should have type %t" (print_ty env t_check'))
    end
  else (* not all_tagged *)
    begin
      let (zus, t_body') =
        match Equal.as_prod env t_check' with
        | (_::_, _) as xtst -> xtst
        | ([], _) -> Error.typing ~loc "this type %t should be a product" (print_ty env t_check')
      in

      (** [ys] are what got added to the environment, [xts] are what should be
          used to check the body, [abs] comes from the binder, [zus] come from
          the type [t] we're checking against *)
      let rec fold env ctx ys xts abs zus =
        match abs, zus with
        | (x,t)::abs, (z,u)::zus ->

          (* let u = u[x_k-1/z_k-1] in *)
          let u = Tt.unabstract_ty ys 0 u in

          let k ctx t' =
            let t = Judgement.mk_ty ctx t' in
            let y, env = Environment.add_fresh ~loc env x t in
            let t' = Tt.abstract_ty ys 0 t' in
            fold env ctx (y::ys) ((x,t')::xts) abs zus
          in

          begin match t with
            | None ->
              Print.debug "untagged arg %t in lambda, using %t as type"
                (Name.print_ident x)
                (print_ty env u);
              k ctx u
            | Some c ->
              check_ty env c >>=
                (fun (ctxt, t') ->
                 let ctx, eqs = Context.join ctx ctxt in
                 if Equal.equal_ty env t' u
                 then k ctx t'
                 else Error.typing ~loc
                     "in this lambda, the variable %t should have a type equal to@ \
                      %t\nFound type@ %t"
                     (Name.print_ident x) (print_ty env u) (print_ty env t'))
          end

        | [], [] ->
          (* let u = u[x_k-1/z_k-1] in *)
          let t_body' = Tt.unabstract_ty ys 0 t_body' in
          let t_body = Judgement.mk_ty ctx t_body' in
          check env body t_body >>=
            (fun (ctxe, e) ->
             let e = Tt.abstract ys 0 e in
             let xts = List.rev xts in
             let ctx, eqs = Context.join ctx ctxe in
             (* XXX should call Context.abstract somewhere, see infer_lambda *)
             Value.return (ctx, Tt.mk_lambda ~loc xts e t_body'))

        | [], _::_ ->
          let t_body' = Tt.mk_prod_ty ~loc zus t_body' in
          let t_body' = Tt.unabstract_ty ys 0 t_body' in
          let t_body = Judgement.mk_ty ctx t_body' in
          check env body t_body >>=
            (fun (ctxe, e) ->
             let e = Tt.abstract ys 0 e in
             let xts = List.rev xts in
             let ctx, eqs = Context.join ctx ctxe in
             Value.return (ctx, Tt.mk_lambda ~loc xts e t_body'))

        | _::_, [] ->
           Error.typing ~loc
                        "tried to check against a type with a too short abstraction@ %t"
                        (print_ty env t_check')
      in
      fold env ctx_check [] [] abs zus
    end (* not all_tagged *)

(** Suppose [e] has type [t], and [cs] is a list of computations [c1, ..., cn].
    Then [spine env e t cs] computes [xeus], [u] and [v] such that we can make
    a spine from [e], [xeus] and [u], and the type of the resulting expression
    is [v].
  *)
and spine ~loc env (ctx_head, e_head, t_head) cs =
  let (xts, t_result) =
    begin match Equal.as_prod env t_head with
      | (_::_, _) as xtst -> xtst
      | ([], _) ->
         Error.typing ~loc "this expression is applied but its type is not a product"
    end
  in
  let rec fold es xus ctx xts cs =
  match xts, cs with
  | xts, [] ->
     let xus = List.rev xus in
     let u = Tt.mk_prod_ty ~loc xts t_result in
     let e = Tt.mk_spine ~loc e_head xus u (List.rev es)
     and v = Tt.instantiate_ty es 0 u in
     let j = Judgement.mk_term ctx e v in
     Value.return_term j
  | (x, t')::xts, c::cs ->
     let t' = Tt.instantiate_ty es 0 t' in
      check env c (Judgement.mk_ty ctx t') >>=
        (fun (ctxe, e) ->
         let ctx, eqs = Context.join ctx ctxe in
         fold (e :: es) ((x,t') :: xus) ctx xts cs)
  | [], ((_ :: _) as cs) ->
     let xus = List.rev xus in
     let e = Tt.mk_spine ~loc e_head xus t_result (List.rev es)
     and t = Tt.instantiate_ty es 0 t_result in
     let j = Judgement.mk_term ctx e t in
     spine ~loc env j cs
  in
  fold [] [] ctx_head xts cs

and let_bind env xcs =
  let rec fold env' = function
    | [] -> Value.return env'
    | (x,c) :: xcs ->
       (* NB: must use [env] in [infer env c], not [env'] because this is parallel let *)
       (infer env c) >>= (fun v ->
                          let env' = Environment.add_bound x v env' in
                            fold env' xcs)
  in
    fold env xcs

and beta_bind env xscs =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer env c >>= as_term ~loc:(snd c) >>=
         (fun (ctxt, _, t) ->
          (* XXX do something with ctxt *)
          let (xts, (t, e1, e2)) = Equal.as_universal_eq env t in
            let h = Hint.mk_beta ~loc env (xts, (t, e1, e2)) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let env = Environment.add_betas xshs env in
      Print.debug "Installed beta hints@ %t"
          (Print.sequence (fun (tags, (_, h)) ppf ->
            Print.print ppf "@[tags: %s ;@ hint: %t@]"
              (String.concat " " tags)
              (Pattern.print_beta_hint [] h)) "," xshs);
      Value.return env
  in fold [] xscs

and eta_bind env xscs =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer env c >>= as_term ~loc:(snd c) >>=
         (fun (ctxt, _, t) ->
          (* XXX do something with ctxt *)
          let (xts, (t, e1, e2)) = Equal.as_universal_eq env t in
            let h = Hint.mk_eta ~loc env (xts, (t, e1, e2)) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let env = Environment.add_etas xshs env in
      Print.debug "Installed eta hints@ %t"
        (Print.sequence (fun (tags, (_, h)) ppf ->
             Print.print ppf "@[tags: %s ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_eta_hint [] h)) "," xshs);
      Value.return env
  in fold [] xscs

and hint_bind env xscs =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer env c >>= as_term ~loc:(snd c) >>=
         (fun (ctxt, _, t) ->
          (* XXX do something with ctxt *)
          let (xts, (t, e1, e2)) = Equal.as_universal_eq env t in
            let h = Hint.mk_general ~loc env (xts, (t, e1, e2)) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let env = Environment.add_generals xshs env in
      Print.debug "Installed hints@ %t"
        (Print.sequence (fun (tags, (k, h)) ppf ->
             Print.print ppf "@[tags: %s ; keys: %t ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_general_key k)
               (Pattern.print_hint [] h)) "," xshs);
      Value.return env
  in fold [] xscs

and inhabit_bind env xscs =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer env c >>= as_term ~loc:(snd c) >>=
         (fun (ctxt, _, t) ->
          (* XXX do something with ctxt *)
          let xts, t = Equal.as_universal_bracket env t in
            let h = Hint.mk_inhabit ~loc env (xts, t) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let env = Environment.add_inhabits xshs env in
      Print.debug "Installed inhabit hints@ %t"
        (Print.sequence (fun (tags, (_, h)) ppf ->
             Print.print ppf "@[tags: %s ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_inhabit_hint [] h)) "," xshs);
      Value.return env
  in fold [] xscs

and check_ty env c : Judgement.ty Value.result =
  check env c Judgement.ty_ty >>=
  (fun (ctx, e) ->
   let t = Tt.ty e in
   let j = Judgement.mk_ty ctx t in
   Value.return j)


let comp = infer

let comp_value env ((_,loc) as c) =
  let r = comp env c in
  Value.to_value ~loc r

let comp_ty env ((_,loc) as c) =
  let r = check_ty env c in
  Value.to_value ~loc r

let comp_term env ((_,loc) as c) =
  let r = infer env c in
  Value.as_term ~loc (Value.to_value ~loc r)

