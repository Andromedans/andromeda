let rec syn_term ctx (e,loc) =
  begin match e with

    | Input.Var x ->
      begin match Context.lookup x ctx with
        | None -> Error.runtime "unknown name %t" (Print.name x)
        | Some (Context.Entry_free t) -> 
          let e = Syntax.mk_name ~loc x
          in (e, t)
        | Some (Context.Entry_value (Syntax.Judge (e, t))) -> (e, t)
        | Some (Context.Entry_value _) -> Error.runtime "%t should be a term" (Print.name x)
      end

    | Input.Type ->
      let e = Syntax.mk_type ~loc in
        (e, e)

    | Input.Ascribe (e, t) ->
      let t = is_type ctx t in
      let e = check_term ctx e t in
        (e, t)

    | Input.Lambda (x, t, e) ->
      let t1 = is_type ctx t in
      let x, ctx = Context.add_free x t1 ctx in
      let (e, t2) = syn_term ctx e in
      let t2 = Syntax.abstract_ty x t2 in
      let e = Syntax.abstract x e in
      let e' = Syntax.mk_lambda ~loc x t1 t2 e
      and t' = Syntax.mk_prod ~loc x t1 t2 in
        (e', t')

    | Input.App (e1, e2) ->
      let (e1, t1) = syn_term ctx e1 in
      let (x, t11, t12) = Equal.as_prod ctx t1 in
      let e2 = check_term ctx e2 t11 in
      let e' = Syntax.mk_app ~loc x t11 t12 e1 e2
      and t' = Syntax.instantiate_ty e2 t12 in
        (e', t')

    | Input.Prod (x, t1, t2) ->
      let t1 = is_type ctx t1 in
      let x, ctx = Context.add_free x t1 ctx in
      let t2 = is_type ctx t2 in
      let t2 = Syntax.abstract_ty x t2 in
      let e' = Syntax.mk_prod ~loc x t1 t2
      and t' = Syntax.mk_type ~loc in
        (e', t')

    | Input.Eq (e1, e2) ->
      let (e1, t) = syn_term ctx e1 in
      let e2 = check_term ctx e2 t in
      let e' = Syntax.mk_eq ~loc t e1 e2
      and t' = Syntax.mk_type ~loc in
        (e', t')

    | Input.Refl e ->
      let (e, t) = syn_term ctx e in
      let e' = Syntax.mk_refl ~loc t e
      and t' = Syntax.mk_eq ~loc t e e in
        (e', t')

  end


and check_term ctx e t =
  let (e,t') = syn_term ctx e in
    if Equal.equal_ty ctx t' t then
      e
    else
      Error.typing ~loc:(snd e) "this expression should have type %t but has type %t"
        (Print.ty ctx t)
        (Print.ty ctx t')

and is_type ctx e =
  check_term ctx e Syntax.typ

let rec ceval ctx (c,_) =
  begin match c with

    | Input.Let (x, c1, c2) ->
      let v1 = ceval ctx c1 in
      let ctx = Context.add_value x v1 ctx
      in ceval ctx c2

    | Input.Term e ->
      let (e, t) = syn_term ctx e
      in Syntax.Judge (e, t)

  end
