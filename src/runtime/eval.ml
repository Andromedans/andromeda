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

    | Syntax.Bound k ->
       let (x, t) = Context.lookup_bound k ctx in
       let x = Tt.mk_name ~loc x in
         (x, t)

    | Syntax.Meta x ->
       begin
         match Context.lookup_meta x ctx with
           | None -> Error.impossible ~loc "unknown meta variable"
           | Some v -> v
       end

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
                  | Value.Return v -> Context.add_meta x v ctx')
                 ctx cs
     in infer ctx c'

  | Syntax.Ascribe (c, t) ->
     let t = expr_ty ctx t
     in let e = check ctx c t
        in Value.Return (e, t)

  | Syntax.Lambda (abs, c) ->
    let rec fold ctx xts = function
      | [] ->
        begin
          match infer ctx c with
          | Value.Return (e, t) ->
            let xts = List.rev xts in
            let xs = List.map fst xts in
            let e = Tt.abstract xs 0 e
            and t = Tt.abstract_ty xs 0 t in
            let e = Tt.mk_lambda ~loc xts e t
            and t = Tt.mk_prod_ty ~loc xts t
          in
            Value.Return (e, t)
        end
      | (x,t) :: abs ->
        let t = expr_ty ctx t in
        let x, ctx = Context.add_fresh x t ctx in
          fold ctx ((x,t) :: xts) abs
    in
      fold ctx [] abs

  | Syntax.Spine (e, es) ->
    let e, t = expr ctx e in
    let xeus, u, v = spine ctx t es in
    let e = Value.mk_spine ~loc e xeus u in
      Value.Return (e, v)

  | Syntax.Prod (abs, c) -> 
    let rec fold ctx xts = function
      | [] ->
        begin
          let xts = List.rev xts in
          let u = comp_ty ctx c in
          let xs = List.map fst xts in
          let u = Tt.abstract_ty xs 0 u in
          let e = Tt.mk_prod ~loc xts u
          and t = Tt.mk_type_ty ~loc
          in
            Value.Return (e, t)
        end
      | (x,t) :: abs ->
        let t = expr_ty ctx t in
        let x, ctx = Context.add_fresh x t ctx in
          fold ctx ((x,t) :: xts) abs
    in
      fold ctx [] abs

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
      Error.typing ~loc:(snd c) "this expression should have type %t but has type %t"
        (Tt.print_ty t)
        (Tt.print_ty t')

and spine ctx t es = 
  let rec fold ctx xs es t = function
  | [] ->
    let u = Value.abstract xs t in
    let v = Value.instantiate es t in
      xeus, u, v
  | e :: es -> 
    let y, t1, t2 = as_prod ctx t in
    let e = check ctx e t1 in
    let u = Value.abstract xs t1 in
    let v = Value.instantiate 
    let x, ctx = Context.add_fresh y t1 ctx in


    and t = Value.instantiate_ty [e] t in
    let a, u = spine ctx t es in
      (x, (e, t1)) :: a, u

and expr_ty ctx ((_,loc) as e) =
  let (e, t) = expr ctx e
  in
    if Equal.equal_ty ctx t Tt.typ
    then Tt.ty e
    else Error.runtime ~loc "this expression should be a type"

and comp_ty ctx c =
  let e = check ctx c Tt.typ
  in Tt.ty e

let ty = comp_ty
