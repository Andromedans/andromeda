(** Conversion from sugared to desugared input syntax *)

let add_bound x bound = x :: bound

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

let mk_let ~loc w c =
  match w with
  | [] -> c
  | (_::_) as w -> Syntax.Let (w, c), loc

let rec comp constants bound ((c',loc) as c) =
  (* When a computation [c] is desugared we hoist out a list of
     let-bindings [w]. NB: it is important that we first desugar
     all subexpressions of [c] so that we get the correct environment
     with hoisted bindings, and only then we desugar the subcomputations
     of [c]. *)
  let w, c' = match c' with

    | Input.Operation (op, e) ->
      let w, e = expr constants bound e in
      w, Syntax.Operation (op, e)

    | Input.Handle (c, hcs) ->
       let c = comp constants bound c
       and h = handler ~loc constants bound hcs in
       [], Syntax.With (h, c)

    | Input.With (e, c) ->
       let w, e = expr constants bound e in
       let c = comp constants bound c in
       let c = Syntax.shift_comp (List.length w) 0 c in
       w, Syntax.With (e, c)

    | Input.Let (xcs, c2) ->
      let rec fold = function
        | [] -> []
        | (x,c) :: xcs ->
          if List.mem_assoc x xcs
          then
            Error.syntax ~loc "%t is bound more than once" (Name.print_ident x)
          else
            let c = comp constants bound c in
            let xcs = fold xcs in
            (x, c) :: xcs
      in
      let xcs = fold xcs in
      let bound = List.fold_left (fun bound (x,_) -> add_bound x bound) bound xcs in
      let c2 = comp constants bound c2 in
      [], Syntax.Let (xcs, c2)

    | Input.Apply (e1, e2) ->
       let w1, e1 = expr constants bound e1
       and w2, e2 = expr constants bound e2 in
       let k1 = List.length w1
       and k2 = List.length w2 in
       let e1 = Syntax.shift_expr k2 0 e1
       and e2 = Syntax.shift_expr k1 k2 e2 in
       w1 @ w2, Syntax.Apply (e1, e2)

    | Input.Beta (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      [], Syntax.Beta (xscs, c)

    | Input.Eta (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      [], Syntax.Eta (xscs, c)

    | Input.Hint (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      [], Syntax.Hint (xscs, c)

    | Input.Inhabit (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      [], Syntax.Inhabit (xscs, c)

    | Input.Unhint (xs, c) ->
      let c = comp constants bound c in
      [], Syntax.Unhint (xs, c)

    | Input.Ascribe (c, t) ->
      let w, t = expr constants bound t in
      let c = comp constants bound c in
      let c = Syntax.shift_comp (List.length w) 0 c in
      w, Syntax.Ascribe (c, t)

    | Input.Whnf c ->
      let c = comp constants bound c in
      [], Syntax.Whnf c

    | Input.Typeof c ->
      let c = comp constants bound c in
      [], Syntax.Typeof c

    | Input.Lambda (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let ys = List.rev ys in
           let c = comp constants bound c in
          mk_lambda ys c
        | (x, None) :: xs ->
          let bound = add_bound x bound
          and ys = (x, None) :: ys in
          fold bound ys xs
        | (x, Some t) :: xs ->
          let ys = (let t = comp constants bound t in (x, Some t) :: ys)
          and bound = add_bound x bound in
          fold bound ys xs
      in
      [], fold bound [] xs

    | Input.Spine (e, cs) ->
      spine constants bound e cs

    | Input.Prod (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let ys = List.rev ys in
           let c = comp constants bound c in
           mk_prod ys c
        | (x,t) :: xs ->
          let ys = (let t = comp constants bound t in (x, t) :: ys)
          and bound = add_bound x bound in
          fold bound ys xs
      in
      [], fold bound [] xs

    | Input.Eq (c1, c2) ->
      let c1 = comp constants bound c1
      and c2 = comp constants bound c2 in
      [], Syntax.Eq (c1, c2)

    | Input.Refl c ->
      let c = comp constants bound c in
      [], Syntax.Refl c

    | Input.Bracket c ->
      let c = comp constants bound c in
      [], Syntax.Bracket c

    | Input.Inhab ->
      [], Syntax.Inhab

    | (Input.Var _ | Input.Type | Input.Function _ | Input.Handler _) ->
      let w, e = expr constants bound c in
      w, Syntax.Return e

  in
  mk_let ~loc w (c', loc)

(* Desguar a spine. This function is a bit messy because we need to untangle
   to constants. But it's worth doing to make users happy. *)
and spine constants bound ((e',loc) as e) cs =
  (* Auxiliary function which splits a list into two parts with k
     elements in the first part. *)
  let rec split k lst =
    if k = 0 then
      [], lst
    else
      match lst with
        | [] -> Error.syntax ~loc "this constant needs %d more arguments" k
        | x::lst -> let lst, lst' = split (k-1) lst in (x :: lst, lst')
  in
  (* First we calculate the head of the spine, and the remaining arguments. *)
  let (w, e), cs =
    begin
      match e' with
      | Input.Var x when not (List.mem x bound) ->
        begin
          try
            let k = List.assoc x constants in
            let cs', cs = split k cs in
              (* We make a constant from [x] and [cs'] *)
              constant ~loc constants bound x cs', cs
          with Not_found -> expr constants bound e, cs
        end
      | _ -> expr constants bound e, cs
    end in
  (* Process the remaining arguments. *)
  let k = List.length w in
  let cs = List.map (fun c -> Syntax.shift_comp k 0 (comp constants bound c)) cs in
  w, Syntax.Spine (e, cs)

(* Desugar handler cases. *)
and handler ~loc constants bound hcs =
  let rec fold val_case op_cases finally_case = function
    | [] -> val_case, op_cases, finally_case

    | Input.CaseVal (x, c) :: hcs ->
       begin match val_case with
       | Some _ -> Error.syntax ~loc:(snd c) "value is handled more than once"
       | None ->
          let c = comp constants (add_bound x bound) c in
          fold (Some (x,c)) op_cases finally_case hcs
       end

    | Input.CaseOp (op, x, k, c) :: hcs ->
       if List.mem_assoc op op_cases
       then
         Error.syntax ~loc:(snd c) "operation %s is handled more than once" op
       else
         let bound = add_bound x bound in
         let bound = add_bound k bound in
         let c = comp constants bound c in
         fold val_case ((op, (x, k, c)) :: op_cases) finally_case hcs

    | Input.CaseFinally (x, c) :: hcs ->
       begin match finally_case with
       | Some _ -> Error.syntax ~loc:(snd c) "more than one finally case"
       | None ->
          let c = comp constants (add_bound x bound) c in
          fold val_case op_cases (Some (x,c)) hcs
       end

  in
  let handler_val, handler_ops, handler_finally = fold None [] None hcs in
  Syntax.Handler (Syntax.{handler_val; handler_ops; handler_finally}), loc

(* Make constant as if it were in an expression position *)
and constant ~loc constants bound x cs =
  let cs = List.map (comp constants bound) cs in
  let c = Syntax.Constant (x, cs), loc
  and y = Name.fresh_candy () in
  [(y, c)], (Syntax.Bound 0, loc)

(* Desugar an expression. It hoists out subcomputations appearing in the
   expression. *)
and expr constants bound ((e', loc) as e) =
  match e' with
  | Input.Var x ->
    begin
      (* a bound variable always shadows a name *)
      match Name.index_of_ident x bound with
      | None ->
        (* it is a constants operation of arity 0 *)
        begin
          try
            let k = List.assoc x constants in
            if k = 0 then constant ~loc constants bound x []
            else Error.syntax ~loc "this constant needs %d more arguments" k
          with Not_found ->
            Error.syntax ~loc "unknown name %t" (Name.print_ident x)
        end
      | Some k -> [], (Syntax.Bound k, loc)
    end

  | Input.Type ->
    [], (Syntax.Type, loc)

  | Input.Function (xs, c) ->
     let rec fold bound = function
       | [] -> Error.impossible "empty function abstraction in desugar"
       | [x] ->
          let bound = add_bound x bound in
          let c = comp constants bound c in
            Syntax.Function (x, c), loc
       | x :: ((_ :: _) as xs) ->
          let bound = add_bound x bound in
          let e = fold bound xs in
            Syntax.Function (x, (Syntax.Return e, loc)), loc
     in
       [], fold bound xs

  | Input.Handler hcs ->
     [], handler ~loc constants bound hcs

  | (Input.Let _ | Input.Beta _ | Input.Eta _ | Input.Hint _ | Input.Inhabit _ |
     Input.Unhint _ | Input.Bracket _ | Input.Inhab | Input.Ascribe _ | Input.Lambda _ |
     Input.Spine _ | Input.Prod _ | Input.Eq _ | Input.Refl _ | Input.Operation _ |
     Input.Whnf _ | Input.Apply _ | Input.Handle _ | Input.With _ | Input.Typeof _) ->
    let x = Name.fresh_candy ()
    and c = comp constants bound e in
    [(x,c)], (Syntax.Bound 0, loc)

let toplevel constants bound (d', loc) =
  let d' = match d' with

    | Input.Axiom (x, yts, u) ->
      let rec fold bound yts' = function
        | [] ->
          let u = comp constants bound u in
          let yts' = List.rev yts' in
          (yts', u)
        | (y, reducing, t) :: yts ->
          let t = comp constants bound t in
          let bound = add_bound y bound
          and yts' = (y, reducing, t) :: yts' in
          fold bound yts' yts
      in
      let yts, u = fold bound [] yts in
      Syntax.Axiom (x, yts, u)

    | Input.TopLet (x, yts, u, ((_, loc) as c)) ->
      let c = match u with
        | None -> c
        | Some u ->
          Input.Ascribe (c, u), loc in
      let yts = List.map (fun (y, t) -> y, Some t) yts in
      let c = Input.Lambda (yts, c), loc in
      let c = comp constants bound c in
      Syntax.TopLet (x, c)

    | Input.TopCheck c ->
      let c = comp constants bound c in
      Syntax.TopCheck c

    | Input.TopBeta xscs ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      Syntax.TopBeta xscs

    | Input.TopEta xscs ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      Syntax.TopEta xscs

    | Input.TopHint xscs ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      Syntax.TopHint xscs

    | Input.TopInhabit xscs ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      Syntax.TopInhabit xscs

    | Input.TopUnhint xs -> Syntax.TopUnhint xs

    | Input.Quit -> Syntax.Quit

    | Input.Help -> Syntax.Help

    | Input.Verbosity n -> Syntax.Verbosity n

    | Input.Include fs -> Syntax.Include fs

    | Input.Environment -> Syntax.Environment

  in
  d', loc
