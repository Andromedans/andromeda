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

(** A filter that verifies the result is a judgement. *)
let as_judge ~loc k v =
  let (e, t) = Value.as_judge ~loc v in
    k e t

(** Evaluation of expressions. *)
let rec expr env (e',loc) =
  let close x c v =
    let env = Environment.add_bound x v env in
    infer env c
  in
  begin
    match e' with

    | Syntax.Bound k -> Environment.lookup_bound k env

    | Syntax.Type ->
      let t = Tt.mk_type ~loc in
      Value.Judge (t, Tt.typ)

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
     let_bind env xcs (fun env -> infer env c)

  | Syntax.Apply (e1, e2) ->
     let v1 = Value.as_closure ~loc (expr env e1)
     and v2 = expr env e2 in
       v1 v2

  | Syntax.Beta (xscs, c) ->
    beta_bind env xscs (fun env -> infer env c)

  | Syntax.Eta (xscs, c) ->
    eta_bind env xscs (fun env -> infer env c)

  | Syntax.Hint (xscs, c) ->
    hint_bind env xscs (fun env -> infer env c)

  | Syntax.Inhabit (xscs, c) ->
    inhabit_bind env xscs (fun env -> infer env c)

  | Syntax.Unhint (xs, c) ->
    let env = Environment.unhint xs env in
    infer env c

  | Syntax.Whnf c ->
    infer env c >>= as_judge ~loc
    (fun e (Tt.Ty t) ->
      let e = Equal.whnf env e
      and t = Equal.whnf env t in
      Value.return_judge e (Tt.ty t))

  | Syntax.Typeof c ->
    infer env c >>= as_judge ~loc
    (fun _ (Tt.Ty t) ->
      Value.return_judge t (Tt.mk_type_ty ~loc))

  | Syntax.Ascribe (c, t) ->
     let t = expr_ty env t in
       check env c t

  | Syntax.Constant (x, cs) ->
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
        Value.return_judge e u

      | (y,(reducing,t))::yts, c::cs ->
        let t = Tt.instantiate_ty es 0 t in
        check env c t >>= as_judge ~loc
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

  | Syntax.Lambda (abs, c) ->
    infer_lambda env loc abs c Value.return_judge

  | Syntax.Spine (e, []) ->
      Value.Return (expr env e)

  | Syntax.Spine (e, cs) ->
    let e, t = Value.as_judge ~loc (expr env e) in
    spine ~loc env e t cs

  | Syntax.Prod (abs, c) ->
    let rec fold env ys xts = function
      | [] ->
         infer_ty env c
           (fun u ->
            let u = Tt.abstract_ty ys 0 u in
            let e = Tt.mk_prod ~loc xts u
            and t = Tt.mk_type_ty ~loc in
            Value.return_judge e t)
      | (x,t) :: abs ->
        let t = expr_ty env t in
        let y, env = Environment.add_fresh ~loc env x t in
        let t = Tt.abstract_ty ys 0 t in
          fold env (y::ys) (xts @ [(x,t)]) abs
    in
      fold env [] [] abs

  | Syntax.Eq (c1, c2) ->
     infer env c1 >>= as_judge ~loc:(snd c1)
       (fun e1 t1 ->
        check env c2 t1 >>= as_judge ~loc:(snd c2)
          (fun e2 _ ->
           let t = Tt.mk_eq ~loc t1 e1 e2 in
             Value.return_judge t Tt.typ))

  | Syntax.Refl c ->
     infer env c >>= as_judge ~loc:(snd c)
       (fun e t ->
        let e' = Tt.mk_refl ~loc t e
        and t' = Tt.mk_eq_ty ~loc t e e in
        Value.return_judge e' t')

  | Syntax.Bracket c ->
    infer_ty env c
      (fun t ->
       let t = Tt.mk_bracket ~loc t in
       Value.return_judge t Tt.typ)

  | Syntax.Inhab ->
    Error.typing ~loc "cannot infer the type of []"

and check env ((c',loc) as c) t : Value.result =
  let return e = Value.return_judge e t in

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

    infer env c >>= as_judge ~loc
      (fun e t' ->
       if Equal.equal_ty env t t'
       then return e
       else Error.typing ~loc:(snd e)
                         "this expression should have type@ %t@ but has type@ %t"
                         (print_ty env t) (print_ty env t'))

  | Syntax.Operation (op, e) ->
     let ve = expr env e
     and k v =
       let (e', t') = Value.as_judge ~loc v in
       if Equal.equal_ty env t t'
       then return e'
       else Error.typing ~loc:(snd e')
                         "this expression should have type@ %t@ but has type@ %t"
                         (print_ty env t) (print_ty env t')
     in
       Value.Operation (op, ve, k)

  | Syntax.Let (xcs, c) ->
     let_bind env xcs
              (fun env ->
               (* We have here a sanity check, namely that [t] does not contain any
                  de Bruijn incides. If it did, we would have to shift it. *)
                  let (Tt.Ty (_, loc) as t') = Tt.shift_ty (List.length xcs) 0 t in
                    if not (Equal.alpha_equal_ty t t') then
                      Error.fatal ~loc "Type %t contains de Bruijn indices in a let-binding" (print_ty env t) ;
                 check env c t')

  | Syntax.Beta (xscs, c) ->
     beta_bind env xscs (fun env -> check env c t)

  | Syntax.Eta (xscs, c) ->
    eta_bind env xscs (fun env -> check env c t)

  | Syntax.Hint (xscs, c) ->
    hint_bind env xscs (fun env -> check env c t)

  | Syntax.Inhabit (xscs, c) ->
    inhabit_bind env xscs (fun env -> check env c t)

  | Syntax.Unhint (xs, c) ->
    let env = Environment.unhint xs env in
    check env c t

  | Syntax.Whnf c ->
    check env c t >>= as_judge ~loc
    (fun e _ ->
       let e = Equal.whnf env e in
       return e)

  | Syntax.Ascribe (c, t') ->
    let t'' = expr_ty env t' in
    (* checking the types for equality right away like this allows to fail
       faster than going through check-infer. *)
    if Equal.equal_ty env t'' t
    then check env c t''
    else Error.typing ~loc:(snd t')
        "this type should be equal to@ %t" (print_ty env t)

  | Syntax.Lambda (abs, c) ->
    check_lambda env loc t abs c

  | Syntax.Refl c ->
    let abs, (t', e1, e2) = Equal.as_universal_eq env t in
    assert (abs = []) ;
    check env c t' >>= as_judge ~loc
      (fun e _ ->
       if Equal.equal env e e1 t'
       then if Equal.equal env e e2 t'
            then return (Tt.mk_refl ~loc t' e)
            else Error.typing ~loc
                   "failed to check that the term@ %t is equal to@ %t"
                   (print_term env e) (print_term env e2)
       else Error.typing ~loc
              "failed to check that the term@ %t is equal to@ %t"
              (print_term env e) (print_term env e1))

  | Syntax.Inhab ->
    begin match Equal.as_bracket env t with
      | Some t' ->
        begin match Equal.inhabit_bracket ~subgoals:true ~loc env t' with
          | Some _ -> return (Tt.mk_inhab ~loc)
          | None -> Error.typing ~loc "do not know how to inhabit %t"
                      (print_ty env t')
        end
      | None -> Error.typing ~loc "[] has a bracket type and not %t"
                  (print_ty env t)
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

and infer_lambda env loc abs c k =
    let rec fold env ys xts = function
      | [] ->
         infer env c >>= as_judge ~loc:(snd c)
           (fun e t ->
            let e = Tt.abstract ys 0 e
            and t = Tt.abstract_ty ys 0 t in
            let e = Tt.mk_lambda ~loc xts e t
            and t = Tt.mk_prod_ty ~loc xts t in
            k e t)
      | (x,c) :: abs ->
        begin match c with
        | None -> Error.typing
            ~loc "cannot infer the type of untagged variable %t" (Name.print_ident x)
        | Some c ->
           check_ty env c >>= as_judge ~loc:(snd c)
             (fun e _ ->
              let t = Tt.ty e in
              let y, env = Environment.add_fresh ~loc env x t in
              let t = Tt.abstract_ty ys 0 t in
              fold env (y::ys) (xts @ [(x,t)]) abs)
        end
    in
      fold env [] [] abs

and check_lambda env loc t abs c =
  (* If the abstractions are fully annotated with types then we
     infer the type of the lambda and compare it to [t],
     otherwise we express [t] as a product and descend into
     the abstraction. *)

  let all_tagged = List.for_all (function (_, None) -> false | (_, Some _) -> true) abs in

  let return e = Value.return_judge e t in

  if all_tagged then
    begin
     (* try to infer and check equality. this might not be the end of the
       story, [as_*] could be operations *)
     (* for instance, an alternative would be to make a fresh pi-type and check
       whether the type at hand [t] is equal to the fresh pi by a general hint,
       and then continue with that one *)

     (* XXX this generalisation should be done also in [fold] below and in
        [spine], same for other [as_*] functions  *)

      infer_lambda env loc abs c
        (fun e' t' ->
         if Equal.equal_ty env t t'
         then return e'
         else Error.typing ~loc
               "this expression is an abstraction but should have type %t" (print_ty env t))
    end
  else (* not all_tagged *)
    begin
      let (zus, v) =
        match Equal.as_prod env t with
        | (_::_, _) as xtst -> xtst
        | ([], _) -> Error.typing ~loc "this type %t should be a product" (print_ty env t)
      in

      (** [ys] are what got added to the environment, [xts] are what should be
          used to check the body, [abs] comes from the binder, [zus] come from
          the type [t] we're checking against *)
      let rec fold env ys xts abs zus =
        match abs, zus with
        | (x,t)::abs, (z,u)::zus ->

          (* let u = u[x_k-1/z_k-1] in *)
          let u = Tt.unabstract_ty ys 0 u in

          let k t =
            let y, env = Environment.add_fresh ~loc env x t in
            let t = Tt.abstract_ty ys 0 t in
            fold env (y::ys) ((x,t)::xts) abs zus
          in

          begin match t with
            | None ->
              Print.debug "untagged arg %t in lambda, using %t as type"
                (Name.print_ident x)
                (print_ty env u);
              k u
            | Some t ->
              check_ty env t >>= as_judge ~loc:(snd t)
                (fun e _ ->
                 let t = Tt.ty e in
                 if Equal.equal_ty env t u
                 then k t
                 else Error.typing ~loc
                     "in this lambda, the variable %t should have a type equal to@ \
                      %t\nFound type@ %t"
                     (Name.print_ident x) (print_ty env u) (print_ty env t))
          end

        | [], [] ->
          (* let u = u[x_k-1/z_k-1] in *)
          let v' = Tt.unabstract_ty ys 0 v in
          check env c v' >>= as_judge ~loc:(snd c)
            (fun e _ ->
             let e = Tt.abstract ys 0 e in
             let xts = List.rev xts in
             return (Tt.mk_lambda ~loc xts e v))

        | [], _::_ ->
          let v = Tt.mk_prod_ty ~loc zus v in
          let v' = Tt.unabstract_ty ys 0 v in
          check env c v' >>= as_judge ~loc:(snd c)
            (fun e _ ->
             let e = Tt.abstract ys 0 e in
             let xts = List.rev xts in
             return (Tt.mk_lambda ~loc xts e v))

        | _::_, [] ->
           Error.typing ~loc
                        "tried to check against a type with a too short abstraction@ %t"
                        (print_ty env t)
      in
      fold env [] [] abs zus
    end (* not all_tagged *)

(** Suppose [e] has type [t], and [cs] is a list of computations [c1, ..., cn].
    Then [spine env e t cs] computes [xeus], [u] and [v] such that we can make
    a spine from [e], [xeus] and [u], and the type of the resulting expression
    is [v].
  *)
and spine ~loc env e t cs =
  (*** XXX Investigate possible use of Equal.as_deep_prod here: it costs more
       but generates possibly longer spines. *)
  let (xts, t) =
    begin match Equal.as_prod env t with
      | (_::_, _) as xtst -> xtst
      | ([], _) ->
         Error.typing ~loc "this expression is applied but its type is not a product"
    end
  in
  let rec fold es xus xts cs =
  match xts, cs with
  | xts, [] ->
      let u = Tt.mk_prod_ty ~loc xts t in
      let e = Tt.mk_spine ~loc e xus u (List.rev es)
      and v = Tt.instantiate_ty es 0 u in
      Value.return_judge e v
  | (x,t)::xts, c::cs ->
      check env c (Tt.instantiate_ty es 0 t) >>= as_judge ~loc:(snd c)
        (fun e _ ->
         let u = t in
         fold (e :: es) (xus @ [(x, u)]) xts cs)
  | [], ((_ :: _) as cs) ->
      let e = Tt.mk_spine ~loc e xus t (List.rev es)
      and t = Tt.instantiate_ty es 0 t in
      spine ~loc env e t cs
  in
  fold [] [] xts cs

and let_bind env xcs k =
  let rec fold env' = function
    | [] -> k env'
    | (x,c) :: xcs ->
       (* NB: must use [env] in [infer env c], not [env'] because this is parallel let *)
       (infer env c) >>= (fun v ->
                          let env' = Environment.add_bound x v env' in
                            fold env' xcs)
  in
    fold env xcs

and beta_bind env xscs k =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer env c >>= as_judge ~loc:(snd c)
         (fun _ t ->
          let (xts, (t, e1, e2)) = Equal.as_universal_eq env t in
            let h = Hint.mk_beta ~loc env (xts, (t, e1, e2)) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let env = Environment.add_betas xshs env in
      Print.debug "Installed beta hints@ %t"
          (Print.sequence (fun (tags, (_, h)) ppf ->
            Print.print ppf "@[tags: %s ;@ hint: %t@]"
              (String.concat " " tags)
              (Pattern.print_beta_hint [] h)) "," xshs);
      k env
  in fold [] xscs

and eta_bind env xscs k =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer env c >>= as_judge ~loc:(snd c)
         (fun _ t ->
          let (xts, (t, e1, e2)) = Equal.as_universal_eq env t in
            let h = Hint.mk_eta ~loc env (xts, (t, e1, e2)) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let env = Environment.add_etas xshs env in
      Print.debug "Installed eta hints@ %t"
        (Print.sequence (fun (tags, (_, h)) ppf ->
             Print.print ppf "@[tags: %s ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_eta_hint [] h)) "," xshs);
      k env
  in fold [] xscs

and hint_bind env xscs k =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer env c >>= as_judge ~loc:(snd c)
         (fun _ t ->
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
      k env
  in fold [] xscs

and inhabit_bind env xscs k =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer env c >>= as_judge ~loc:(snd c)
         (fun _ t ->
          let xts, t = Equal.as_universal_bracket env t in
            let h = Hint.mk_inhabit ~loc env (xts, t) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let env = Environment.add_inhabits xshs env in
      Print.debug "Installed inhabit hints@ %t"
        (Print.sequence (fun (tags, (_, h)) ppf ->
             Print.print ppf "@[tags: %s ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_inhabit_hint [] h)) "," xshs);
      k env
  in fold [] xscs

and expr_ty env ((_,loc) as e) =
  let (e, t) = Value.as_judge ~loc (expr env e) in
  if Equal.equal_ty env t Tt.typ
  then Tt.ty e
  else
    Error.runtime ~loc
      "this expression should be a type but its type is %t"
      (print_ty env t)

and check_ty env ((_,loc) as c) =
  check env c Tt.typ

and infer_ty env c k =
  check env c Tt.typ >>= as_judge ~loc:(snd c)
    (fun e _ -> k (Tt.ty e))

let comp = infer

let comp_value env ((_,loc) as c) =
  let r = comp env c in
  Value.to_value ~loc r

let ty env ((_,loc) as c) =
  let r = check env c Tt.typ in
  let (e, _) = Value.as_judge ~loc (Value.to_value ~loc r) in
    Tt.ty e
