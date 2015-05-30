(** Conversion from sugared to desugared input syntax *)

type ctx = Name.t list

let add_bound x ctx = x :: ctx

let rec mk_lambda ys ((c', loc) as c) =
  match ys with
  | [] -> c'
  | _ :: _ ->
    begin match c' with
      | Syntax.Lambda (ys', c) -> mk_lambda (ys @ ys') c
      | _ -> Syntax.Lambda (ys, c)
    end

let rec mk_prod ys ((t', loc) as t) =
  match ys with
  | [] -> t'
  | _ :: _ ->
    begin match t' with
      | Syntax.Prod (ys', t) -> mk_prod (ys @ ys') t
      | _ -> Syntax.Prod (ys, t)
    end

let mk_let ~loc w c' =
  match w with
  | [] -> c', loc
  | _ :: _ -> Syntax.Let (w, (c', loc)), loc

let rec comp ctx ((c',loc) as c) =
  (* When a computation [c] is desugared we hoist out a list of
     let-bindings [w]. NB: it is important that we first desugar
     all subexpressions of [c] so that we get the correct context
     with hoisted bindings, and only then we desugar the subcomputations
     of [c]. *)
  let w, c = match c' with

    | Input.Let (xcs, c2) ->
      let rec fold = function
        | [] -> []
        | (x,c) :: xcs ->
          if List.mem_assoc x xcs
          then
            Error.syntax ~loc "%t is bound more than once" (Name.print x)
          else
            let c = comp ctx c in
            let xcs = fold xcs in
            (x, c) :: xcs
      in
      let xcs = fold xcs in
      let ctx = List.fold_left (fun ctx (x,_) -> add_bound x ctx) ctx xcs in
      let c2 = comp ctx c2 in
      [], Syntax.Let (xcs, c2)

    | Input.Beta (e, c) ->
      let ctx, w, e = expr ctx e in
      let c = comp ctx c in
        w, Syntax.Beta (e, c)

    | Input.Eta (e, c) ->
      let ctx, w, e = expr ctx e in
      let c = comp ctx c in
        w, Syntax.Eta (e, c)

    | Input.Hint (e, c) ->
      let ctx, w, e = expr ctx e in
      let c = comp ctx c in
        w, Syntax.Hint (e, c)

    | Input.Inhabit (e, c) ->
      let ctx, w, e = expr ctx e in
      let c = comp ctx c in
        w, Syntax.Inhabit (e, c)

    | Input.Ascribe (c, t) ->
      let ctx, w, t = expr ctx t in
      let c = comp ctx c in
      w, Syntax.Ascribe (c, t)

    | Input.Lambda (xs, c) ->
      let rec fold ctx ys = function
        | [] ->
          let c = comp ctx c in
          mk_lambda ys c
        | (x, None) :: xs ->
          let ctx = add_bound x ctx
          and ys = ys @ [(x, None)] in
          fold ctx ys xs
        | (x, Some t) :: xs ->
          begin
            match expr ctx t with
            | _, [], t ->
              let ctx = add_bound x ctx
              and ys = ys @ [(x, Some t)] in
              fold ctx ys xs
            | ctx, w, ((_,loc) as t) ->
              let c = fold (add_bound x ctx) [] xs in
              let c = Syntax.Lambda ([(x, Some t)], (c, loc)) in
              let c = mk_let ~loc w c in
              mk_lambda ys c
          end
      in
      [], fold ctx [] xs

    | Input.Spine (e, cs) ->
      let ctx, w, e = expr ctx e in
      let cs = List.map (comp ctx) cs in
      w, Syntax.Spine (e, cs)

    | Input.Prod (xs, c) ->
      let rec fold ctx ys = function
        | [] ->
          let c = comp ctx c in
          mk_prod ys c
        | (x,t) :: xs ->
          begin
            match expr ctx t with
            | _, [], t ->
              let ctx = add_bound x ctx
              and ys = ys @ [(x,t)] in
              fold ctx ys xs
            | ctx, w, ((_,loc) as t) ->
              let c = fold (add_bound x ctx) [] xs in
              let c = Syntax.Prod ([(x,t)], (c,loc)) in
              let c = mk_let ~loc:(snd t) w c in
              mk_prod ys c
          end
      in
      [], fold ctx [] xs

    | Input.Eq (c1, c2) ->
      let c1 = comp ctx c1
      and c2 = comp ctx c2 in
      [], Syntax.Eq (c1, c2)

    | Input.Refl c ->
      let c = comp ctx c in
      [], Syntax.Refl c

    | Input.Bracket c ->
      let c = comp ctx c in
      [], Syntax.Bracket c

    | Input.Inhab ->
      [], Syntax.Inhab

    | (Input.Var _ | Input.Type) ->
      let _, w, e = expr ctx c in
      w, Syntax.Return e

  in
  mk_let ~loc w c

and expr ctx ((e', loc) as e) =
  match e' with
  | Input.Var x ->
    begin
      match Name.index_of x ctx with
      | None -> ctx, [], (Syntax.Name x, loc)
      | Some k -> ctx, [], (Syntax.Bound k, loc)
    end

  | Input.Type ->
    ctx, [], (Syntax.Type, loc)

  | (Input.Let _ | Input.Beta _ | Input.Eta _ | Input.Hint _ | Input.Inhabit _ |
     Input.Bracket _ | Input.Inhab | Input.Ascribe _ | Input.Lambda _ |
     Input.Spine _ | Input.Prod _ | Input.Eq _ | Input.Refl _) ->
    let x = Name.fresh Name.anonymous
    and c = comp ctx e in
    let ctx = add_bound x ctx in
    ctx, [(x,c)], (Syntax.Bound 0, loc)

let toplevel ctx (d', loc) =
  let d' = match d' with

    | Input.Parameter (xs, t) ->
      let c = comp ctx t in
      Syntax.Parameter (xs, c)

    | Input.TopLet (x, c) ->
      let c = comp ctx c in
      Syntax.TopLet (x, c)

    | Input.TopCheck c ->
      let c = comp ctx c in
      Syntax.TopCheck c

    | Input.TopBeta c ->
      let c = comp ctx c in
      Syntax.TopBeta c

    | Input.TopEta c ->
      let c = comp ctx c in
      Syntax.TopEta c

    | Input.TopHint c ->
      let c = comp ctx c in
      Syntax.TopHint c

    | Input.TopInhabit c ->
      let c = comp ctx c in
      Syntax.TopInhabit c

    | Input.Quit -> Syntax.Quit

    | Input.Help -> Syntax.Help

    | Input.Context -> Syntax.Context

  in
  d', loc
