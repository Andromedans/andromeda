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
    | Syntax.Name x ->
       begin
         match Context.lookup_free x ctx with
         | None -> Error.runtime ~loc "unknown free variable %t" (Name.print x)
         | Some t ->
            let x = Tt.mk_name ~loc x in
              (x, t)
       end

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

  | Syntax.Let (cs, c') ->
     let ctx = List.fold_left
                 (fun ctx' (x,c) ->
                  (* NB: must use [ctx] here, not [ctx'] *)
                  match infer ctx c with
                  | Value.Return v -> Context.add_bound x v ctx')
                 ctx cs
     in infer ctx c'

  | Syntax.Beta (e, c) ->
    let (_, t) = expr ctx e in
    let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
    let h = Pattern.make_beta_hint ~loc (xts, (t, e1, e2)) in
    let ctx = Context.add_beta h ctx in
    Print.debug "Installed beta hint %t"
      (Pattern.print_beta_hint [] h);
      infer ctx c

  | Syntax.Eta (e, c) ->
    let (_, t) = expr ctx e in
    let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
    let h = Pattern.make_eta_hint ~loc (xts, (t, e1, e2)) in
    let ctx = Context.add_eta h ctx in
    Print.debug "Installed eta hint %t"
      (Pattern.print_eta_hint [] h);
      infer ctx c

  | Syntax.Hint (e, c) ->
    let (_, t) = expr ctx e in
    let (xts, (t, e1, e2)) = Equal.as_universal_eq ctx t in
    let h = Pattern.make_hint ~loc (xts, (t, e1, e2)) in
    let ctx = Context.add_hint h ctx in
    Print.debug "Installed hint %t"
      (Pattern.print_hint [] h);
      infer ctx c

  | Syntax.Ascribe (c, t) ->
     let t = expr_ty ctx t
     in let e = check ctx c t
        in Value.Return (e, t)

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
        let t = expr_ty ctx t in
        let y, ctx = Context.add_fresh x t ctx in
        let ctx = Context.add_bound x (Tt.mk_name ~loc y, t) ctx in
        let t = Tt.abstract_ty ys 0 t in
          fold ctx (y::ys) (xts @ [(x,t)]) abs
    in
      fold ctx [] [] abs

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

  | Syntax.Eq (e1, c2) ->
    let (e1, t1) = expr ctx e1 in
    let e2 = check ctx c2 t1 in
    let t = Tt.mk_eq ~loc t1 e1 e2
    in
      Value.Return (t, Tt.typ)

  | Syntax.Refl e ->
    let (e, t) = expr ctx e
    in let e' = Tt.mk_refl ~loc t e
       and t' = Tt.mk_eq_ty ~loc t e e
       in Value.Return (e', t')

and check ctx c t =
  match infer ctx c with
  | Value.Return (e, t') ->
     if Equal.equal_ty ctx t' t
     then e
     else
      Error.typing ~loc:(snd c) "this expression (%t) should have type %t but has type %t"
        (print_term ctx e)
        (print_ty ctx t)
        (print_ty ctx t')

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
      | None -> Error.typing ~loc "an expression is applied but it is not a function"
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

and expr_ty ctx ((_,loc) as e) =
  let (e, t) = expr ctx e
  in
    if Equal.equal_ty ctx t Tt.typ
    then Tt.ty e
    else
      Error.runtime ~loc
        "this expression should be a type but its type is %t"
        (print_ty ctx t)


and infer_ty ctx c =
  let e = check ctx c Tt.typ in
    Tt.ty e

let comp = infer

let ty = infer_ty
