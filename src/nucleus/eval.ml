(** Evaluation of computations *)

(** Auxiliary printing functions. *)

let print_term ctx e =
    let xs = Context.used_names ctx in
      Tt.print_term xs e

let print_ty ctx t =
    let xs = Context.used_names ctx in
      Tt.print_ty xs t

(** Evaluation of expressions. *)
let rec expr ctx (e',loc) =
  begin
    match e' with

    | Syntax.Bound k -> Context.lookup_bound k ctx

    | Syntax.Type ->
      let t = Tt.mk_type ~loc
      in (t, Tt.typ)
  end

(** Evaluate a computation -- infer mode. *)
let rec infer ctx (c',loc) =
  match c' with

  | Syntax.Return e ->
     let v = expr ctx e
     in Value.Return v

  | Syntax.Let (xcs, c) ->
     let ctx = let_bind ctx xcs in
     infer ctx c

  | Syntax.Beta (xscs, c) ->
    let ctx = beta_bind ctx xscs in
    infer ctx c

  | Syntax.Eta (xscs, c) ->
    let ctx = eta_bind ctx xscs in
    infer ctx c

  | Syntax.Hint (xscs, c) ->
    let ctx = hint_bind ctx xscs in
    infer ctx c

  | Syntax.Inhabit (xscs, c) ->
    let ctx = inhabit_bind ctx xscs in
    infer ctx c

  | Syntax.Ascribe (c, t) ->
     let t = expr_ty ctx t
     in let e = check ctx c t
        in Value.Return (e, t)

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
        Value.Return (e, u)

      | (y,(reducing,t))::yts, c::cs ->
        let t = Tt.instantiate_ty es 0 t in
        let e = check ctx c t in
        let e = if reducing then Equal.whnf ctx e else e in
        fold (e :: es) yts cs

      | _::_, [] ->
        Error.typing ~loc "too few arguments in a primitive operation (%d missing)"
          (List.length yts)

      | _, _::_ ->
        Error.typing ~loc "too many arguments in a primitive operation (%d extra)"
          (List.length cs)
    in
    fold [] yts cs

  | Syntax.Lambda (abs, c) ->
    let rec fold ctx ys xts = function
      | [] ->
        begin
          match infer ctx c with
          | Value.Return (e, t) ->
            let e = Tt.abstract ys 0 e
            and t = Tt.abstract_ty ys 0 t in
            let e = Tt.mk_lambda ~loc xts e t
            and t = Tt.mk_prod_ty ~loc xts t in
              Value.Return (e, t)
        end
      | (x,t) :: abs ->
        begin match t with
        | None -> Error.typing
            ~loc "cannot infer the type of untagged variable %t" (Name.print x)
        | Some t ->
          let t = check_ty ctx t in
          let y, ctx = Context.add_fresh x t ctx in
          let ctx = Context.add_bound x (Tt.mk_name ~loc y, t) ctx in
          let t = Tt.abstract_ty ys 0 t in
          fold ctx (y::ys) (xts @ [(x,t)]) abs
        end
    in
      fold ctx [] [] abs

  | Syntax.Spine (e, []) ->
    let e, t = expr ctx e in
      Value.Return (e, t)

  | Syntax.Spine (e, cs) ->
    let e, t = expr ctx e in
    let (e, v) = spine ~loc ctx e t cs in
    Value.Return (e, v)

  | Syntax.Prod (abs, c) ->
    let rec fold ctx ys xts = function
      | [] ->
        let u = infer_ty ctx c in
        let u = Tt.abstract_ty ys 0 u in
        let e = Tt.mk_prod ~loc xts u
        and t = Tt.mk_type_ty ~loc
        in
          Value.Return (e, t)
      | (x,t) :: abs ->
        let t = expr_ty ctx t in
        let y, ctx = Context.add_fresh x t ctx in
        let ctx = Context.add_bound x (Tt.mk_name ~loc y, t) ctx in
        let t = Tt.abstract_ty ys 0 t in
          fold ctx (y::ys) (xts @ [(x,t)]) abs
    in
      fold ctx [] [] abs

  | Syntax.Eq (c1, c2) ->
    begin match infer ctx c1 with
      | Value.Return (e1, t1) ->
        let e2 = check ctx c2 t1 in
        let t = Tt.mk_eq ~loc t1 e1 e2 in
        Value.Return (t, Tt.typ)
    end

  | Syntax.Refl c ->
    begin match infer ctx c with
      | Value.Return (e,t) ->
        let e' = Tt.mk_refl ~loc t e
        and t' = Tt.mk_eq_ty ~loc t e e
        in Value.Return (e', t')
    end

  | Syntax.Bracket c ->
    let t = infer_ty ctx c in
    let t = Tt.mk_bracket ~loc t in
    Value.Return (t, Tt.typ)

  | Syntax.Inhab ->
    Error.typing ~loc "cannot infer the type of []"

and check ctx ((c',loc) as c) t =
  match c' with

  | Syntax.Return _
  | Syntax.PrimApp _
  | Syntax.Prod _
  | Syntax.Eq _
  | Syntax.Spine _
  | Syntax.Bracket _  ->
    (** this is the [check-infer] rule, which applies for all term formers "foo"
        that don't have a "check-foo" rule *)

    let Value.Return (e',t') = infer ctx c in
    if Equal.equal_ty ctx t t'
    then e'
    else Error.typing ~loc:(snd e')
        "this expression should have type@ %t but has type@ %t"
        (print_ty ctx t) (print_ty ctx t')

  | Syntax.Let (xcs, c) ->
    let ctx = let_bind ctx xcs in
    let t' = Tt.shift_ty (List.length xcs) 0 t in

    (* XXX looks like shift is dead code. good terms don't expose their indices *)
    if not (Equal.equal_ty ctx t t') then
      Print.message ~verbosity:3
        "Let shifted@ %t into@ %t" (print_ty ctx t) (print_ty ctx t');
    let t = t' in

    check ctx c t

  | Syntax.Beta (xscs, c) ->
    let ctx = beta_bind ctx xscs in
    check ctx c t

  | Syntax.Eta (xscs, c) ->
    let ctx = eta_bind ctx xscs in
    check ctx c t

  | Syntax.Hint (xscs, c) ->
    let ctx = hint_bind ctx xscs in
    check ctx c t

  | Syntax.Inhabit (xscs, c) ->
    let ctx = inhabit_bind ctx xscs in
    check ctx c t

  | Syntax.Ascribe (c, t') ->
    let t'' = expr_ty ctx t' in
    (* checking the types for equality right away like this allows to fail
       faster than going through check-infer. *)
    if Equal.equal_ty ctx t'' t
    then check ctx c t''
    else Error.typing ~loc:(snd t')
        "this type should be equal to %t" (print_ty ctx t)

  | Syntax.Lambda (abs, c) ->
    check_lambda ctx loc t abs c

  | Syntax.Refl c ->
    let abs, (t, e1, e2) = Equal.as_universal_eq ctx t in
    assert (abs = []);
    let e = check ctx c t in
    let err e' =
      Error.typing ~loc
        "failed to check that the term@ %t is equal to@ %t"
        (print_term ctx e) (print_term ctx e') in
    if not @@ Equal.equal ctx e e1 t
    then err e1
    else if not @@ Equal.equal ctx e e2 t
    then err e2
    else Tt.mk_refl ~loc t e

  | Syntax.Inhab ->
    begin match Equal.as_bracket ctx t with
      | Some t ->
        begin match Equal.inhabit_bracket ~subgoals:true ~loc ctx t with
          | Some _ -> Tt.mk_inhab ~loc
          | None -> Error.typing ~loc "do not know how to inhabit %t"
                      (print_ty ctx t)
        end
      | None -> Error.typing ~loc "[] has a bracket type and not %t"
                  (print_ty ctx t)
    end

and check_lambda ctx loc t abs c =
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
      let t =
        begin match t with
        | None ->
           Print.debug "untagged arg %t in lambda, using %t as type"
             (Name.print x)
             (print_ty ctx u);
           u
        | Some t ->
          let t = check_ty ctx t in
          if Equal.equal_ty ctx t u then t
          else Error.typing ~loc
              "in this lambda, the variable %t should have a type equal to@ \
               %t\nFound type@ %t"
              (Name.print x) (print_ty ctx u) (print_ty ctx t)
        end in

      let y, ctx = Context.add_fresh x t ctx in
      let ctx = Context.add_bound x (Tt.mk_name ~loc y, t) ctx in
      let t = Tt.abstract_ty ys 0 t in
      fold ctx (y::ys) (z::zs) ((x,t)::xts) abs zus v

    | [], [] ->
      (* let u = u[x_k-1/z_k-1] in *)
      let v' = Tt.unabstract_ty ys 0 v in
      let e = check ctx c v' in
      let e = Tt.abstract ys 0 e in
      let xts = List.rev xts in
      Tt.mk_lambda ~loc xts e v

    | [], _::_ ->
      let v = Tt.mk_prod_ty ~loc zus v in
      let v' = Tt.unabstract_ty ys 0 v in
      let e = check ctx c v' in
      let e = Tt.abstract ys 0 e in
      let xts = List.rev xts in
      Tt.mk_lambda ~loc xts e v

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
      (e, v)
  | (x,t)::xts, c::cs ->
      let e = check ctx c (Tt.instantiate_ty es 0 t)
      and u = t in
      fold (e :: es) (xus @ [(x, u)]) xts cs
  | [], ((_ :: _) as cs) ->
      let e = Tt.mk_spine ~loc e xus t (List.rev es)
      and t = Tt.instantiate_ty es 0 t in
      spine ~loc ctx e t cs
  in
  fold [] [] xts cs

and let_bind ctx xcs =
  List.fold_left
    (fun ctx' (x,c) ->
        (* NB: must use [ctx] here, not [ctx'] *)
        match infer ctx c with
          | Value.Return v -> Context.add_bound x v ctx')
    ctx xcs


and beta_bind ctx xscs =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
      let Value.Return (_, t) = infer ctx c in
      let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
      let h = Hint.mk_beta ~loc ctx (xts, (t, e1, e2)) in
      fold ((xs, h) :: xshs) xscs
    | [] -> let ctx = Context.add_betas xshs ctx in
      Print.debug "Installed beta hints@ %t"
          (Print.sequence (fun (tags, (_, h)) ppf ->
            Print.print ppf "@[tags: %s ;@ hint: %t@]"
              (String.concat " " tags)
              (Pattern.print_beta_hint [] h)) "," xshs);
      ctx
  in fold [] xscs

and eta_bind ctx xscs =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
      let Value.Return (_, t) = infer ctx c in
      let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
      let h = Hint.mk_eta ~loc ctx (xts, (t, e1, e2)) in
      fold ((xs, h) :: xshs) xscs
    | [] -> let ctx = Context.add_etas xshs ctx in
      Print.debug "Installed eta hints@ %t"
        (Print.sequence (fun (tags, (_, h)) ppf ->
             Print.print ppf "@[tags: %s ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_eta_hint [] h)) "," xshs);
      ctx
  in fold [] xscs

and hint_bind ctx xscs =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
      let Value.Return (_, t) = infer ctx c in
      let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
      let h = Hint.mk_general ~loc ctx (xts, (t, e1, e2)) in
      fold ((xs, h) :: xshs) xscs
    | [] -> let ctx = Context.add_generals xshs ctx in
      Print.debug "Installed hints@ %t"
        (Print.sequence (fun (tags, (_, h)) ppf ->
             Print.print ppf "@[tags: %s ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_hint [] h)) "," xshs);
      ctx
  in fold [] xscs

and inhabit_bind ctx xscs =
  let rec fold xshs = function
    | (xs, ((_,loc) as c)) :: xscs ->
      let Value.Return (_, t) = infer ctx c in
      let xts, t = Equal.as_universal_bracket ctx t in
      let h = Hint.mk_inhabit ~loc ctx (xts, t) in
      fold ((xs, h) :: xshs) xscs
    | [] -> let ctx = Context.add_inhabits xshs ctx in
      Print.debug "Installed inhabit hints@ %t"
        (Print.sequence (fun (tags, (_, h)) ppf ->
             Print.print ppf "@[tags: %s ;@ hint: %t@]"
               (String.concat " " tags)
               (Pattern.print_inhabit_hint [] h)) "," xshs);
      ctx
  in fold [] xscs

and expr_ty ctx ((_,loc) as e) =
  let (e, t) = expr ctx e
  in
    if Equal.equal_ty ctx t Tt.typ
    then Tt.ty e
    else
      Error.runtime ~loc
        "this expression should be a type but its type is %t"
        (print_ty ctx t)

and check_ty ctx ((_,loc) as e) =
  Tt.ty @@ check ctx e Tt.typ

and infer_ty ctx c =
  let e = check ctx c Tt.typ in
    Tt.ty e

let comp = infer

let ty = infer_ty
