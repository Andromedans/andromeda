(** Evaluation of computations *)

(** Auxiliary printing functions. *)

let print_term ctx e =
    let xs = Context.used_names ctx in
      Tt.print_term xs e

let print_ty ctx t =
    let xs = Context.used_names ctx in
      Tt.print_ty xs t

(** Notation for the monadic bind *)
let (>>=) = Value.bind

(** A filter that verifies the result is a judgement. *)
let as_judge ~loc k v =
  let (e, t) = Value.as_judge ~loc v in
    k e t

(** Evaluation of expressions. *)
let rec expr ctx (e',loc) =
  begin
    match e' with

    | Syntax.Bound k -> Context.lookup_bound k ctx

    | Syntax.Type ->
      let t = Tt.mk_type ~loc in
      Value.Judge (t, Tt.typ)

    | Syntax.Function (x, c) ->
       let f v =
         let ctx = Context.add_bound x v ctx in
         infer ctx c
       in
       Value.Closure f
  end

(** Evaluate a computation -- infer mode. *)
and infer ctx (c',loc) =
  match c' with

  | Syntax.Return e ->
     let v = expr ctx e in
     Value.Return v

  | Syntax.Operation (op, e) ->
     let v = expr ctx e in
     let k u = Value.Return u in
     Value.Operation (op, v, k)

  | Syntax.Handle (c, hcs) ->
     let r = infer ctx c in
     handle_result ctx hcs r

  | Syntax.Let (xcs, c) ->
     let_bind ctx xcs (fun ctx -> infer ctx c)

  | Syntax.Apply (e1, e2) ->
     let v1 = Value.as_closure ~loc (expr ctx e1)
     and v2 = expr ctx e2 in
       v1 v2

  | Syntax.Beta (xscs, c) ->
    beta_bind ctx xscs (fun ctx -> infer ctx c)

  | Syntax.Eta (xscs, c) ->
    eta_bind ctx xscs (fun ctx -> infer ctx c)

  | Syntax.Hint (xscs, c) ->
    hint_bind ctx xscs (fun ctx -> infer ctx c)

  | Syntax.Inhabit (xscs, c) ->
    inhabit_bind ctx xscs (fun ctx -> infer ctx c)

  | Syntax.Unhint (xs, c) ->
    let ctx = Context.unhint xs ctx in
    infer ctx c

  | Syntax.Whnf c ->
    infer ctx c >>= as_judge ~loc
    (fun e (Tt.Ty t) ->
      let e = Equal.whnf ctx e
      and t = Equal.whnf ctx t in
      Value.return_judge e (Tt.ty t))

  | Syntax.Ascribe (c, t) ->
     let t = expr_ty ctx t in
       check ctx c t

  | Syntax.PrimApp (x, cs) ->
    let yts, u =
      begin match Context.lookup_primitive x ctx with
      | Some ytsu -> ytsu
      | None -> Error.typing "unknown operation %t" (Name.print x)
      end in
    let rec fold es yts cs =
      match yts, cs with
      | [], [] ->
        let u = Tt.instantiate_ty es 0 u
        and e = Tt.mk_primapp ~loc x (List.rev es) in
        Value.return_judge e u

      | (y,(reducing,t))::yts, c::cs ->
        let t = Tt.instantiate_ty es 0 t in
        check ctx c t >>= as_judge ~loc
          (fun e _ ->
           let e = if reducing then Equal.whnf ctx e else e in
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
    infer_lambda ctx loc abs c Value.return_judge

  | Syntax.Spine (e, []) ->
      Value.Return (expr ctx e)

  | Syntax.Spine (e, cs) ->
    let e, t = Value.as_judge ~loc (expr ctx e) in
    spine ~loc ctx e t cs

  | Syntax.Prod (abs, c) ->
    let rec fold ctx ys xts = function
      | [] ->
         infer_ty ctx c
           (fun u ->
            let u = Tt.abstract_ty ys 0 u in
            let e = Tt.mk_prod ~loc xts u
            and t = Tt.mk_type_ty ~loc in
            Value.return_judge e t)
      | (x,t) :: abs ->
        let t = expr_ty ctx t in
        let y, yt = Value.fresh ~loc x t in
        let ctx = Context.add_bound x yt ctx in
        let t = Tt.abstract_ty ys 0 t in
          fold ctx (y::ys) (xts @ [(x,t)]) abs
    in
      fold ctx [] [] abs

  | Syntax.Eq (c1, c2) ->
     infer ctx c1 >>= as_judge ~loc:(snd c1)
       (fun e1 t1 ->
        check ctx c2 t1 >>= as_judge ~loc:(snd c2)
          (fun e2 _ ->
           let t = Tt.mk_eq ~loc t1 e1 e2 in
             Value.return_judge t Tt.typ))

  | Syntax.Refl c ->
     infer ctx c >>= as_judge ~loc:(snd c)
       (fun e t ->
        let e' = Tt.mk_refl ~loc t e
        and t' = Tt.mk_eq_ty ~loc t e e in
        Value.return_judge e' t')

  | Syntax.Bracket c ->
    infer_ty ctx c
      (fun t ->
       let t = Tt.mk_bracket ~loc t in
       Value.return_judge t Tt.typ)

  | Syntax.Inhab ->
    Error.typing ~loc "cannot infer the type of []"

and check ctx ((c',loc) as c) t : Value.result =
  let return e = Value.return_judge e t in

  match c' with

  | Syntax.Return _
  | Syntax.Handle _
  | Syntax.Apply _
  | Syntax.PrimApp _
  | Syntax.Prod _
  | Syntax.Eq _
  | Syntax.Spine _
  | Syntax.Bracket _  ->
    (** this is the [check-infer] rule, which applies for all term formers "foo"
        that don't have a "check-foo" rule *)

    infer ctx c >>= as_judge ~loc
      (fun e t' ->
       if Equal.equal_ty ctx t t'
       then return e
       else Error.typing ~loc:(snd e)
                         "this expression should have type@ %t@ but has type@ %t"
                         (print_ty ctx t) (print_ty ctx t'))

  | Syntax.Operation (op, e) ->
     let ve = expr ctx e
     and k v =
       let (e', t') = Value.as_judge ~loc v in
       if Equal.equal_ty ctx t t'
       then return e'
       else Error.typing ~loc:(snd e')
                         "this expression should have type@ %t@ but has type@ %t"
                         (print_ty ctx t) (print_ty ctx t')
     in
       Value.Operation (op, ve, k)

  | Syntax.Let (xcs, c) ->
     let_bind ctx xcs
              (fun ctx ->
               (* We have here a sanity check, namely that [t] does not contain any
                  de Bruijn incides. If it did, we would have to shift it. *)
                  let (Tt.Ty (_, loc) as t') = Tt.shift_ty (List.length xcs) 0 t in
                    if not (Equal.alpha_equal_ty t t') then
                      Error.fatal ~loc "Type %t contains de Bruijn indices in a let-binding" (print_ty ctx t) ;
                 check ctx c t')

  | Syntax.Beta (xscs, c) ->
     beta_bind ctx xscs (fun ctx -> check ctx c t)

  | Syntax.Eta (xscs, c) ->
    eta_bind ctx xscs (fun ctx -> check ctx c t)

  | Syntax.Hint (xscs, c) ->
    hint_bind ctx xscs (fun ctx -> check ctx c t)

  | Syntax.Inhabit (xscs, c) ->
    inhabit_bind ctx xscs (fun ctx -> check ctx c t)

  | Syntax.Unhint (xs, c) ->
    let ctx = Context.unhint xs ctx in
    check ctx c t

  | Syntax.Whnf c ->
    check ctx c t >>= as_judge ~loc
    (fun e _ ->
       let e = Equal.whnf ctx e in
       return e)

  | Syntax.Ascribe (c, t') ->
    let t'' = expr_ty ctx t' in
    (* checking the types for equality right away like this allows to fail
       faster than going through check-infer. *)
    if Equal.equal_ty ctx t'' t
    then check ctx c t''
    else Error.typing ~loc:(snd t')
        "this type should be equal to@ %t" (print_ty ctx t)

  | Syntax.Lambda (abs, c) ->
    check_lambda ctx loc t abs c

  | Syntax.Refl c ->
    let abs, (t', e1, e2) = Equal.as_universal_eq ctx t in
    assert (abs = []) ;
    check ctx c t' >>= as_judge ~loc
      (fun e _ ->
       if Equal.equal ctx e e1 t'
       then if Equal.equal ctx e e2 t'
            then return (Tt.mk_refl ~loc t' e)
            else Error.typing ~loc
                   "failed to check that the term@ %t is equal to@ %t"
                   (print_term ctx e) (print_term ctx e2)
       else Error.typing ~loc
              "failed to check that the term@ %t is equal to@ %t"
              (print_term ctx e) (print_term ctx e1))

  | Syntax.Inhab ->
    begin match Equal.as_bracket ctx t with
      | Some t' ->
        begin match Equal.inhabit_bracket ~subgoals:true ~loc ctx t' with
          | Some _ -> return (Tt.mk_inhab ~loc)
          | None -> Error.typing ~loc "do not know how to inhabit %t"
                      (print_ty ctx t')
        end
      | None -> Error.typing ~loc "[] has a bracket type and not %t"
                  (print_ty ctx t)
    end

and handle_result ctx hcs r =
  let {Syntax.handle_case_val=hval;
       Syntax.handle_case_ops=hops;
       Syntax.handle_case_finally=hfin} = hcs
  in
  begin match r with
  | Value.Return v ->
     begin match hval with
           | Some (x,c) ->
              let ctx = Context.add_bound x v ctx in
              infer ctx c
           | None -> r
     end
  | Value.Operation (op, ve, cont) ->
     let hcs' = { hcs with Syntax.handle_case_finally = None } in
     let wrap cont v = handle_result ctx hcs' (cont v) in
     begin
       try
         let (x, k, c) = List.assoc op hops in
         let ctx = Context.add_bound x ve ctx in
         let ctx = Context.add_bound k (Value.Closure (wrap cont)) ctx in
         infer ctx c
       with
         Not_found -> 
         Value.Operation (op, ve, (wrap cont))
     end
  end >>=
    (fun v -> 
     match hfin with
           | Some (x,c) ->
              let ctx = Context.add_bound x v ctx in
              infer ctx c
           | None -> Value.Return v)

and infer_lambda ctx loc abs c k =
    let rec fold ctx ys xts = function
      | [] ->
         infer ctx c >>= as_judge ~loc:(snd c)
           (fun e t ->
            let e = Tt.abstract ys 0 e
            and t = Tt.abstract_ty ys 0 t in
            let e = Tt.mk_lambda ~loc xts e t
            and t = Tt.mk_prod_ty ~loc xts t in
            k e t)
      | (x,c) :: abs ->
        begin match c with
        | None -> Error.typing
            ~loc "cannot infer the type of untagged variable %t" (Name.print x)
        | Some c ->
           check_ty ctx c >>= as_judge ~loc:(snd c)
             (fun e _ ->
              let t = Tt.ty e in
              let y, yt = Value.fresh ~loc x t in
              let ctx = Context.add_bound x yt ctx in
              let t = Tt.abstract_ty ys 0 t in
              fold ctx (y::ys) (xts @ [(x,t)]) abs)
        end
    in
      fold ctx [] [] abs

and check_lambda ctx loc t abs c =
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

      infer_lambda ctx loc abs c
        (fun e' t' ->
         if Equal.equal_ty ctx t t'
         then return e'
         else Error.typing ~loc
               "this expression is an abstraction but should have type %t" (print_ty ctx t))
    end
  else (* not all_tagged *)
    begin
      let (zus, v) = match Equal.as_prod ctx t with
        | Some x -> x
        | None -> Error.typing ~loc
                    "this type %t should be a product" (print_ty ctx t)
      in

      (** [ys] are what got added to the environment, [zus] come from the type
          [t] we're checking against, [abs] from the binder, [xts] are what
          should be used to check the body *)
      let rec fold ctx ys zs xts abs zus v =
        match abs, zus with
        | (x,t)::abs, (z,u)::zus ->

          (* let u = u[x_k-1/z_k-1] in *)
          let u = Tt.unabstract_ty ys 0 u in

          let k t =
            let y, yt = Value.fresh ~loc x t in
            let ctx = Context.add_bound x yt ctx in
            let t = Tt.abstract_ty ys 0 t in
            fold ctx (y::ys) (z::zs) ((x,t)::xts) abs zus v
          in

          begin match t with
            | None ->
              Print.debug "untagged arg %t in lambda, using %t as type"
                (Name.print x)
                (print_ty ctx u);
              k u
            | Some t ->
              check_ty ctx t >>= as_judge ~loc:(snd t)
                (fun e _ ->
                 let t = Tt.ty e in
                 if Equal.equal_ty ctx t u
                 then k t
                 else Error.typing ~loc
                     "in this lambda, the variable %t should have a type equal to@ \
                      %t\nFound type@ %t"
                     (Name.print x) (print_ty ctx u) (print_ty ctx t))
          end

        | [], [] ->
          (* let u = u[x_k-1/z_k-1] in *)
          let v' = Tt.unabstract_ty ys 0 v in
          check ctx c v' >>= as_judge ~loc:(snd c)
            (fun e _ ->
             let e = Tt.abstract ys 0 e in
             let xts = List.rev xts in
             return (Tt.mk_lambda ~loc xts e v))

        | [], _::_ ->
          let v = Tt.mk_prod_ty ~loc zus v in
          let v' = Tt.unabstract_ty ys 0 v in
          check ctx c v' >>= as_judge ~loc:(snd c)
            (fun e _ ->
             let e = Tt.abstract ys 0 e in
             let xts = List.rev xts in
             return (Tt.mk_lambda ~loc xts e v))

        | _::_, [] ->
          let v = Equal.as_prod ctx v in
          begin match v with
            | None ->
              Error.typing ~loc
                "tried to check against a type with a too short abstraction@ %t"
                (print_ty ctx t)
            | Some (zus, v) -> fold ctx ys zs xts abs zus v
          end
      in
      fold ctx [] [] [] abs zus v
    end (* not all_tagged *)

(** Suppose [e] has type [t], and [cs] is a list of computations [c1, ..., cn].
    Then [spine ctx e t cs] computes [xeus], [u] and [v] such that we can make
    a spine from [e], [xeus] and [u], and the type of the resulting expression
    is [v].
  *)
and spine ~loc ctx e t cs =
  (*** XXX Investigate possible use of Equal.as_deep_prod here: it costs more
       but generates possibly longer spines. *)
  let (xts, t) =
    begin match Equal.as_prod ctx t with
      | Some (xts, t) -> xts, t
      | None -> Error.typing ~loc "this expression is applied but it is not a function"
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
      check ctx c (Tt.instantiate_ty es 0 t) >>= as_judge ~loc:(snd c)
        (fun e _ ->
         let u = t in
         fold (e :: es) (xus @ [(x, u)]) xts cs)
  | [], ((_ :: _) as cs) ->
      let e = Tt.mk_spine ~loc e xus t (List.rev es)
      and t = Tt.instantiate_ty es 0 t in
      spine ~loc ctx e t cs
  in
  fold [] [] xts cs

and let_bind ctx xcs k =
  let rec fold ctx' = function
    | [] -> k ctx'
    | (x,c) :: xcs ->
       (* NB: must use [ctx] in [infer ctx c], not [ctx'] because this is parallel let *)
       (infer ctx c) >>= (fun v ->
                          let ctx' = Context.add_bound x v ctx' in
                            fold ctx' xcs)
  in
    fold ctx xcs

and beta_bind ctx xscs k =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer ctx c >>= as_judge ~loc:(snd c)
         (fun _ t ->
          let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
            let h = Hint.mk_beta ~loc ctx (xts, (t, e1, e2)) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let ctx = Context.add_betas xshs ctx in
      Print.debug "Installed beta hints@ %t"
          (Print.sequence (fun (tags, (_, h)) ppf ->
            Print.print ppf "@[tags: %s ;@ hint: %t@]"
              (String.concat " " tags)
              (Pattern.print_beta_hint [] h)) "," xshs);
      k ctx
  in fold [] xscs

and eta_bind ctx xscs k =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer ctx c >>= as_judge ~loc:(snd c)
         (fun _ t ->
          let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
            let h = Hint.mk_eta ~loc ctx (xts, (t, e1, e2)) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let ctx = Context.add_etas xshs ctx in
      Print.debug "Installed eta hints@ %t"
        (Print.sequence (fun (tags, (_, h)) ppf ->
             Print.print ppf "@[tags: %s ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_eta_hint [] h)) "," xshs);
      k ctx
  in fold [] xscs

and hint_bind ctx xscs k =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer ctx c >>= as_judge ~loc:(snd c)
         (fun _ t ->
          let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
            let h = Hint.mk_general ~loc ctx (xts, (t, e1, e2)) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let ctx = Context.add_generals xshs ctx in
      Print.debug "Installed hints@ %t"
        (Print.sequence (fun (tags, (k, h)) ppf ->
             Print.print ppf "@[tags: %s ; keys: %t ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_general_key k)
               (Pattern.print_hint [] h)) "," xshs);
      k ctx
  in fold [] xscs

and inhabit_bind ctx xscs k =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
       infer ctx c >>= as_judge ~loc:(snd c)
         (fun _ t ->
          let xts, t = Equal.as_universal_bracket ctx t in
            let h = Hint.mk_inhabit ~loc ctx (xts, t) in
              fold ((xs, h) :: xshs) xscs)
    | [] -> let ctx = Context.add_inhabits xshs ctx in
      Print.debug "Installed inhabit hints@ %t"
        (Print.sequence (fun (tags, (_, h)) ppf ->
             Print.print ppf "@[tags: %s ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_inhabit_hint [] h)) "," xshs);
      k ctx
  in fold [] xscs

and expr_ty ctx ((_,loc) as e) =
  let (e, t) = Value.as_judge ~loc (expr ctx e) in
  if Equal.equal_ty ctx t Tt.typ
  then Tt.ty e
  else
    Error.runtime ~loc
      "this expression should be a type but its type is %t"
      (print_ty ctx t)

and check_ty ctx ((_,loc) as c) =
  check ctx c Tt.typ

and infer_ty ctx c k =
  check ctx c Tt.typ >>= as_judge ~loc:(snd c)
    (fun e _ -> k (Tt.ty e))
          
let comp = infer

let comp_value ctx ((_,loc) as c) =
  let r = comp ctx c in
  Value.to_value ~loc r

let ty ctx ((_,loc) as c) =
  let r = check ctx c Tt.typ in
  let (e, _) = Value.as_judge ~loc (Value.to_value ~loc r) in
    Tt.ty e
