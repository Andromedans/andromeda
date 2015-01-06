(** Evaluation of expressions. *)
let rec expr ctx (e',loc) =
  begin
    match e' with
    | Syntax.Free x ->
       begin
         match Context.lookup_free x ctx with
         | None -> Error.runtime ~loc "unknown free variable %s" (Common.to_string x)
         | Some t -> 
            let x = Value.mk_name ~loc x in
              (x, t)
       end

    | Syntax.Bound _ ->
       Error.impossible ~loc "bound variable encountered"

    | Syntax.Meta x ->
       begin
         match Context.lookup_meta x ctx with
           | None -> Error.impossible ~loc "unknown meta variable"
           | Some v -> v
       end

    | Syntax.Type ->
       let t = Value.mk_type ~loc
       in (t, Value.typ)
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
                  | Value.Return v -> Context.add_meta x v ctx')
                 ctx cs
     in infer ctx c'

  | Syntax.Ascribe (c, t) ->
     let t = ty_of_expr ctx t
     in let e = check ctx c t
        in Value.Return (e, t)

  | Syntax.Lambda (abs, c) -> Error.unimplemented ~loc "Inference for lambdas not implemented"

  | Syntax.Spine (e, es) -> Error.unimplemented ~loc "Inference for spines not implemented"

  | Syntax.Prod (abs, c) -> Error.unimplemented ~loc "Inference for products not implemented"

  | Syntax.Eq (e1, c2) ->
    let (e1, t1) = expr ctx e1 in
    let e2 = check ctx c2 t1 in
    let t = Value.mk_eq ~loc t1 e1 e2
    in
      Value.Return (t, Value.typ)

  | Syntax.Refl e ->
    let (e, t) = expr ctx e
    in let e' = Value.mk_refl ~loc t e
       and t' = Value.mk_eq_ty ~loc t e e
       in Value.Return (e', t')

and check ctx c t =
  match infer ctx c with
  | Value.Return (e, t') ->
     if Equal.equal_ty ctx t' t
     then e
     else 
      Error.typing ~loc:(snd c) "this expression should have type %t but has type %t"
        (Print.ty ctx t)
        (Print.ty ctx t')

and ty_of_expr ctx ((_,loc) as e) =
  let (e, t) = expr ctx e
  in
    if Equal.equal_ty ctx t Value.typ
    then Value.ty e
    else Error.runtime ~loc "this expression should be a type"

let ty ctx c =
  let e = check ctx c Value.typ
  in Value.ty e
