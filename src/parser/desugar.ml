(** Conversion from sugared to desugared input syntax *)

module IntSet = Set.Make (struct
                    type t = int
                    let compare = compare
                  end)

module IdentMap = Name.IdentMap

let add_bound x bound = x :: bound

let rec mk_lambda ~loc ys ((c', _) as c) =
  match ys with
  | [] -> c
  | _ :: _ ->
    begin match c' with
      | Syntax.Lambda (ys', c) -> mk_lambda ~loc (ys @ ys') c
      | _ -> Syntax.Lambda (ys, c), loc
    end

let rec mk_prod ~loc ys ((t', _) as t) =
  match ys with
  | [] -> t
  | _ :: _ ->
    begin match t' with
      | Syntax.Prod (ys', t) -> mk_prod ~loc (ys @ ys') t
      | _ -> Syntax.Prod (ys, t), loc
    end

(* n is the length of vars *)
let rec tt_pattern (env : Value.Env.t) bound vars n (p,loc) =
  match p with
    | Input.Tt_Anonymous ->
      (Syntax.Tt_Anonymous, loc), vars, n

    | Input.Tt_As (p,x) ->
      begin try
        let i = List.assoc x vars in
        let p, vars, n = tt_pattern env bound vars n p in
        (Syntax.Tt_As (p,i), loc), vars, n
      with | Not_found ->
        let i = n in
        let p, vars, n = tt_pattern env bound ((x,n)::vars) (n+1) p in
        (Syntax.Tt_As (p,i), loc), vars, n
      end

    | Input.Tt_Var x ->
      begin try
        let i = List.assoc x vars in
        (Syntax.Tt_As ((Syntax.Tt_Anonymous, loc), i), loc), vars, n
      with | Not_found ->
        (Syntax.Tt_As ((Syntax.Tt_Anonymous, loc), n), loc), ((x,n)::vars), (n+1)
      end

    | Input.Tt_Type ->
      (Syntax.Tt_Type, loc), vars, n

    | Input.Tt_Name x ->
      begin match Name.index_of_ident x bound with
        | Some k -> (Syntax.Tt_Bound k, loc), vars, n
        | None ->
           begin
             match Value.Env.lookup_constant x env with
               | Some (lst, _) ->
                  if List.length lst = 0 then
                    (Syntax.Tt_Constant x, loc), vars, n
                  else
                    Error.syntax ~loc "matching against constant %t is not implemented" (Name.print_ident x)
               | None -> Error.syntax ~loc "unknown name %t" (Name.print_ident x)
           end
      end

    | Input.Tt_Lambda (b,x,popt,p) ->
      let popt, vars, n = match popt with
        | None ->
          None, vars, n
        | Some p ->
          let p, vars, n = tt_pattern env bound vars n p in
          Some p, vars, n
        in
      let bopt, vars, n =
        if b
        then
          try
            (* XXX it might be a good idea to warn if x is already a pattern variable, since that should never match. *)
            let i = List.assoc x vars in
            Some i, vars, n
          with | Not_found ->
            Some n, ((x,n)::vars), (n+1)
        else None, vars, n
      in
      let p, vars, n = tt_pattern env (add_bound x bound) vars n p in
      (Syntax.Tt_Lambda (x,bopt,popt,p), loc), vars, n

    | Input.Tt_App (p1,p2) ->
      let p1, vars, n = tt_pattern env bound vars n p1 in
      let p2, vars, n = tt_pattern env bound vars n p2 in
      (Syntax.Tt_App (p1,p2), loc), vars, n

    | Input.Tt_Prod (b,x,popt,p) ->
      let popt, vars, n = match popt with
        | None ->
          None, vars, n
        | Some p ->
          let p, vars, n = tt_pattern env bound vars n p in
          Some p, vars, n
        in
      let bopt, vars, n =
        if b
        then
          try
            let i = List.assoc x vars in
            Some i, vars, n
          with | Not_found ->
            Some n, ((x,n)::vars), (n+1)
        else None, vars, n
      in
      let p, vars, n = tt_pattern env (add_bound x bound) vars n p in
      (Syntax.Tt_Prod (x,bopt,popt,p), loc), vars, n

    | Input.Tt_Eq (p1,p2) ->
      let p1, vars, n = tt_pattern env bound vars n p1 in
      let p2, vars, n = tt_pattern env bound vars n p2 in
      (Syntax.Tt_Eq (p1,p2), loc), vars, n

    | Input.Tt_Refl p ->
      let p, vars, n = tt_pattern env bound vars n p in
      (Syntax.Tt_Refl p, loc), vars, n

    | Input.Tt_Signature xps ->
      let rec fold bound vars n xps = function
        | [] ->
          let xps = List.rev xps in
          (Syntax.Tt_Signature xps, loc), vars, n
        | (l,b,xopt,p)::rem ->
          let x = match xopt with | Some x -> x | None -> l in
          let bopt, vars, n =
            if b
            then
              try
                let i = List.assoc x vars in
                Some i, vars, n
              with | Not_found ->
                Some n, ((x,n)::vars), (n+1)
            else None, vars, n
          in
          let p, vars, n = tt_pattern env bound vars n p in
          fold (add_bound x bound) vars n ((l,x,bopt,p)::xps) rem
        in
      fold bound vars n [] xps

    | Input.Tt_Structure xps ->
      let rec fold bound vars n xps = function
        | [] ->
          let xps = List.rev xps in
          (Syntax.Tt_Structure xps, loc), vars, n
        | (l,b,xopt,p)::rem ->
          let x = match xopt with | Some x -> x | None -> l in
          let bopt, vars, n =
            if b
            then
              try
                let i = List.assoc x vars in
                Some i, vars, n
              with | Not_found ->
                Some n, ((x,n)::vars), (n+1)
            else None, vars, n
          in
          let p, vars, n = tt_pattern env bound vars n p in
          fold (add_bound x bound) vars n ((l,x,bopt,p)::xps) rem
        in
      fold bound vars n [] xps

    | Input.Tt_Projection (p,l) ->
      let p, vars, n = tt_pattern env bound vars n p in
      (Syntax.Tt_Projection (p,l), loc), vars, n

let rec pattern (env : Value.Env.t) bound vars n (p,loc) =
  match p with
    | Input.Patt_Anonymous -> (Syntax.Patt_Anonymous, loc), vars, n

    | Input.Patt_As (p,x) ->
      begin try
        let i = List.assoc x vars in
        let p, vars, n = pattern env bound vars n p in
        (Syntax.Patt_As (p,i), loc), vars, n
      with | Not_found ->
        let i = n in
        let p, vars, n = pattern env bound ((x,n)::vars) (n+1) p in
        (Syntax.Patt_As (p,i), loc), vars, n
      end

    | Input.Patt_Var x ->
      begin try
        let i = List.assoc x vars in
        (Syntax.Patt_As ((Syntax.Patt_Anonymous, loc), i), loc), vars, n
      with | Not_found ->
        (Syntax.Patt_As ((Syntax.Patt_Anonymous, loc), n), loc), ((x,n)::vars), (n+1)
      end

    | Input.Patt_Name x ->
      begin match Name.index_of_ident x bound with
        | None ->
          begin match Value.Env.lookup_data x env with
            | Some k ->
              if k = 0
              then (Syntax.Patt_Tag (x,[]), loc), vars, n
              else Error.syntax ~loc "the data constructor %t expects %d arguments but is matched with 0"
                  (Name.print_ident x) k
            | None -> Error.syntax ~loc "unknown value name %t" (Name.print_ident x)
          end
        | Some k ->
            (Syntax.Patt_Bound k, loc), vars, n
      end

    | Input.Patt_Jdg (p1,p2) ->
      let p1, vars, n = tt_pattern env bound vars n p1 in
      let p2, vars, n = tt_pattern env bound vars n p2 in
      (Syntax.Patt_Jdg (p1,p2), loc), vars, n

    | Input.Patt_Tag (t,ps) ->
      let rec fold vars n ps = function
        | [] ->
          let ps = List.rev ps in
          (Syntax.Patt_Tag (t,ps), loc), vars, n
        | p::rem ->
          let p, vars, n = pattern env bound vars n p in
          fold vars n (p::ps) rem
        in
      fold vars n [] ps

    | Input.Patt_Cons (p1, p2) ->
      let p1, vars, n = pattern env bound vars n p1 in
      let p2, vars, n = pattern env bound vars n p2 in
      (Syntax.Patt_Cons (p1,p2), loc), vars, n

    | Input.Patt_List ps ->
       let rec fold ~loc vars n = function
         | [] -> (Syntax.Patt_Nil, loc), vars, n
         | p :: ps ->
            let p, vars, n = pattern env bound vars n p in
            let ps, vars, n = fold ~loc:(snd p) vars n ps in
            (Syntax.Patt_Cons (p, ps), loc), vars, n
       in
       fold ~loc vars n ps

let rec comp ~yield (env : Value.Env.t) bound (c',loc) =
  match c' with
    | Input.Handle (c, hcs) ->
       let c = comp ~yield env bound c
       and h = handler ~loc env bound hcs in
       Syntax.With (h, c), loc

    | Input.With (c1, c2) ->
       let c1 = comp ~yield env bound c1
       and c2 = comp ~yield env bound c2 in
       Syntax.With (c1, c2), loc

    | Input.Let (xcs, c2) ->
      let rec fold = function
        | [] -> []
        | (x,c) :: xcs ->
          if List.mem_assoc x xcs
          then
            Error.syntax ~loc "%t is bound more than once" (Name.print_ident x)
          else
            let c = comp ~yield env bound c in
            let xcs = fold xcs in
            (x, c) :: xcs
      in
      let xcs = fold xcs in
      let bound = List.fold_left (fun bound (x,_) -> add_bound x bound) bound xcs in
      let c2 = comp ~yield env bound c2 in
      Syntax.Let (xcs, c2), loc

    | Input.Lookup c ->
       let c = comp ~yield env bound c in
       Syntax.Lookup c, loc

    | Input.Ref c ->
       let c = comp ~yield env bound c in
       Syntax.Ref c, loc

    | Input.Update (c1, c2) ->
       let c1 = comp ~yield env bound c1
       and c2 = comp ~yield env bound c2 in
       Syntax.Update (c1, c2), loc

    | Input.Sequence (c1, c2) ->
       let c1 = comp ~yield env bound c1
       and c2 = comp ~yield env bound c2 in
       Syntax.Sequence (c1, c2), loc

    | Input.Assume ((x, t), c) ->
       let t = comp ~yield env bound t in
       let bound = add_bound x bound in
       let c = comp ~yield env bound c in
       Syntax.Assume ((x, t), c), loc

    | Input.Where (c1, c2, c3) ->
       let c1 = comp ~yield env bound c1
       and c2 = comp ~yield env bound c2
       and c3 = comp ~yield env bound c3 in
       Syntax.Where (c1, c2, c3), loc

    | Input.Match (c, cases) ->
       let c = comp ~yield env bound c
       and cases = List.map (match_case ~yield env bound) cases in
       Syntax.Match (c, cases), loc

    | Input.Ascribe (c, t) ->
       let t = comp ~yield env bound t
       and c = comp ~yield env bound c in
       Syntax.Ascribe (c, t), loc

    | Input.Reduce c ->
      let c = comp ~yield env bound c in
      Syntax.Reduce c, loc

    | Input.External s ->
       Syntax.External s, loc

    | Input.Typeof c ->
      let c = comp ~yield env bound c in
      Syntax.Typeof c, loc

    | Input.Lambda (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let ys = List.rev ys in
           let c = comp ~yield env bound c in
           mk_lambda ~loc ys c
        | (x, None) :: xs ->
          let bound = add_bound x bound
          and ys = (x, None) :: ys in
          fold bound ys xs
        | (x, Some t) :: xs ->
          let ys = (let t = comp ~yield env bound t in (x, Some t) :: ys)
          and bound = add_bound x bound in
          fold bound ys xs
      in
      fold bound [] xs

    | Input.Spine (e, cs) ->
      spine ~yield env bound e cs

    | Input.Prod (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let ys = List.rev ys in
           let c = comp ~yield env bound c in
           mk_prod ~loc ys c
        | (x,t) :: xs ->
          let ys = (let t = comp ~yield env bound t in (x, t) :: ys)
          and bound = add_bound x bound in
          fold bound ys xs
      in
      fold bound [] xs

    | Input.Eq (c1, c2) ->
      let c1 = comp ~yield env bound c1
      and c2 = comp ~yield env bound c2 in
      Syntax.Eq (c1, c2), loc

    | Input.Refl c ->
      let c = comp ~yield env bound c in
      Syntax.Refl c, loc

    | Input.Signature lst ->
      let rec fold bound labels res = function
        | [] -> List.rev res
        | (x,y,c)::rem ->
          let y = match y with | Some y -> y | None -> x in
          if List.mem x labels
          then Error.syntax ~loc "field %t appears more than once" (Name.print_ident x)
          else if Name.eq_ident x Name.anonymous
          then Error.syntax ~loc "anonymous field"
          else
            let c = comp ~yield env bound c in
            fold (add_bound y bound) (x::labels) ((x,y,c)::res) rem
        in
      let lst = fold bound [] [] lst in
      Syntax.Signature lst, loc

    | Input.Structure lst ->
      let rec fold bound labels res = function
        | [] -> List.rev res
        | (x,y,c) :: rem ->
          let y = match y with | Some y -> y | None -> x in
          if List.mem x labels
          then Error.syntax ~loc "field %t appears more than once" (Name.print_ident x)
          else if Name.eq_ident x Name.anonymous
          then Error.syntax ~loc "anonymous field"
          else
            let c = comp ~yield env bound c in
            fold (add_bound y bound) (x :: labels) ((x,y,c) :: res) rem
        in
      let lst = fold bound [] [] lst in
      Syntax.Structure lst, loc

    | Input.Projection (c,x) ->
      let c = comp ~yield env bound c in
      Syntax.Projection (c,x), loc

    | Input.Var x ->
         (* a bound variable always shadows a name *)
       begin
         match Name.index_of_ident x bound with
         | Some k -> Syntax.Bound k, loc
         | None ->
            begin
              match Value.Env.lookup_decl x env with
              | Some (Value.Constant (lst, _)) ->
                 let k = List.length lst in
                 if k = 0 then constant ~loc ~yield env bound x []
                 else Error.syntax ~loc "this constant needs %d more arguments" k

              | Some (Value.Data k) ->
                 if k = 0 then Syntax.Tag (x, []), loc
                 else Error.syntax ~loc "this constant needs %d more arguments" k

              | Some (Value.Operation k) ->
                 if k = 0 then Syntax.Perform (x, []), loc
                 else Error.syntax ~loc "this operation needs %d more arguments" k

              | None -> Error.syntax ~loc "unknown name %t" (Name.print_ident x)
            end
       end

  | Input.Type ->
    Syntax.Type, loc

  | Input.Yield c ->
    if yield
    then
      let c = comp ~yield env bound c in
      Syntax.Yield c, loc
    else
      Error.syntax ~loc "yield may only be used in a handler"

  | Input.Context ->
     Syntax.Context, loc

  | Input.Function (xs, c) ->
     let rec fold bound = function
       | [] -> comp ~yield env bound c
       | x :: xs ->
          let bound = add_bound x bound in
          let c = fold bound xs in
          Syntax.Function (x, c), loc
     in
       fold bound xs

  | Input.Rec (f, xs, c) ->
     let rec fold bound = function
       | [] -> comp ~yield env bound c
       | y :: ys ->
          let bound = add_bound y bound in
          let c = fold bound ys in
            Syntax.Function (y, c), loc
     in
     begin match xs with
     | [] -> Error.impossible ~loc "empty recursion abstraction in desguar"
     | x :: xs ->
        let bound = add_bound f bound in
        let bound = add_bound x bound in
        let c = fold bound xs in
        Syntax.Rec (f, x, c), loc
     end

  | Input.Handler hcs ->
     handler ~loc env bound hcs

  | Input.Tag (t, cs) ->
     let cs = List.map (comp ~yield env bound) cs in
     Syntax.Tag (t, cs), loc

  | Input.List cs ->
     let rec fold ~loc = function
       | [] -> Syntax.Nil, loc
       | c :: cs ->
          let c = comp ~yield env bound c in
          let cs = fold ~loc:(snd c) cs in
          Syntax.Cons (c, cs), loc
     in
     fold ~loc cs

  | Input.Cons (e1, e2) ->
    let e1 = comp ~yield env bound e1 in
    let e2 = comp ~yield env bound e2 in
    Syntax.Cons (e1,e2), loc

  | Input.Congruence (e1,e2) ->
    let e1 = comp ~yield env bound e1 in
    let e2 = comp ~yield env bound e2 in
    Syntax.Congruence (e1,e2), loc

(* Desguar a spine. This function is a bit messy because we need to untangle
   to env. But it's worth doing to make users happy. *)
and spine ~yield env bound ((c',loc) as c) cs =

  (* Auxiliary function which splits a list into two parts with k
     elements in the first part. *)
  let rec split thing k lst =
    if k = 0 then
      [], lst
    else
      match lst with
        | [] -> Error.syntax ~loc "this %s needs %d more arguments" thing k
        | x::lst -> let lst, lst' = split thing (k-1) lst in (x :: lst, lst')
  in

  (* First we calculate the head of the spine, and the remaining arguments. *)
  let c, cs =
    begin
      match c' with
      | Input.Var x when not (List.mem x bound) ->
         begin
           match Value.Env.lookup_decl x env with

           | Some (Value.Constant (lst, _)) ->
              let k = List.length lst in
              let cs', cs = split "constant" k cs in
              (* We make a constant from [x] and [cs'] *)
              constant ~loc ~yield env bound x cs', cs

           | Some (Value.Data k) ->
              let cs', cs = split "data constructor" k cs in
              (* We make a tag from [x] and [cs'] *)
              tag ~loc ~yield env bound x cs', cs

           | Some (Value.Operation k) ->
              let cs', cs = split "operation" k cs in
              perform ~loc ~yield env bound x cs', cs

           | None ->
              Error.syntax ~loc "unknown identifier %t" (Name.print_ident x)
         end

      | _ -> comp ~yield env bound c, cs
    end in

  let cs = List.map (comp ~yield env bound) cs in
  Syntax.Spine (c, cs), loc

(* Desugar handler cases. *)
and handler ~loc env bound hcs =
  (* for every case | #op p => c we do #op binder => match binder with | p => c end *)
  let rec fold val_cases op_cases finally_cases = function
    | [] ->
      List.rev val_cases, IdentMap.map List.rev op_cases, List.rev finally_cases

    | Input.CaseVal c :: hcs ->
      (* XXX if this handler is in a outer handler's operation case, should we use its yield?
         eg handle ... with | op => handler | val x => yield x end end *)
      let case = match_case ~yield:false env bound c in
      fold (case::val_cases) op_cases finally_cases hcs

    | Input.CaseOp (op, ((ps,_) as c)) :: hcs ->
      begin match Value.Env.lookup_operation op env with
        | Some k ->
          let n = List.length ps in
          if n = k
          then
            let case = multimatch_case ~yield:true env bound c in
            let my_cases = try IdentMap.find op op_cases with | Not_found -> [] in
            let my_cases = case::my_cases in
            fold val_cases (IdentMap.add op my_cases op_cases) finally_cases hcs
          else
            Error.syntax ~loc "operation %t expects %d arguments but was matched with %d" (Name.print_ident op) k n
        | None ->
          Error.syntax ~loc "unknown operation %t" (Name.print_ident op)
      end

    | Input.CaseFinally c :: hcs ->
      let case = match_case ~yield:false env bound c in
      fold val_cases op_cases (case::finally_cases) hcs

  in
  let handler_val, handler_ops, handler_finally = fold [] IdentMap.empty [] hcs in
  Syntax.Handler (Syntax.{handler_val; handler_ops; handler_finally}), loc

(* Desugar a match case *)
and match_case ~yield env bound (p, c) =
  let p, vars, _ = pattern env bound [] 0 p in
  let rec fold xs bound = function
    | [] -> xs, bound
    | (x,_)::rem -> fold (x::xs) (add_bound x bound) rem
    in
  let xs, bound = fold [] bound vars in
  let c = comp ~yield env bound c in
  (xs, p, c)

and multimatch_case ~yield env bound (ps, c) =
  let rec fold_patterns ps vars n = function
    | [] -> List.rev ps, vars, n
    | p::rem ->
      let p, vars, n = pattern env bound vars n p in
      fold_patterns (p::ps) vars n rem
  in
  let ps, vars, _ = fold_patterns [] [] 0 ps in
  let rec fold xs bound = function
    | [] -> xs, bound
    | (x,_)::rem -> fold (x::xs) (add_bound x bound) rem
    in
  let xs, bound = fold [] bound vars in
  let c = comp ~yield env bound c in
  (xs, ps, c)

and constant ~loc ~yield env bound x cs =
  let cs = List.map (comp ~yield env bound) cs in
  Syntax.Constant (x, cs), loc

and tag ~loc ~yield env bound x cs =
  let cs = List.map (comp ~yield env bound) cs in
  Syntax.Tag (x, cs), loc

and perform ~loc ~yield env bound x cs =
  let cs = List.map (comp ~yield env bound) cs in
  Syntax.Perform (x, cs), loc

let toplevel (env : Value.Env.t) bound (d', loc) =
  let d' = match d' with
    | Input.Operation (x, k) -> Syntax.Operation (x, k)

    | Input.Data (x, k) -> Syntax.Data (x, k)

    | Input.Axiom (x, ryts, u) ->
      let rec fold bound ryts' = function
        | [] ->
          let u = comp ~yield:false env bound u in
          let ryts' = List.rev ryts' in
          (ryts', u)
        | (reducing, (y, t)) :: ryts ->
          let t = comp ~yield:false env bound t in
          let bound = add_bound y bound
          and ryts' = (reducing, (y, t)) :: ryts' in
          fold bound ryts' ryts
      in
      let ryts, u = fold bound [] ryts in
      Syntax.Axiom (x, ryts, u)

    | Input.TopHandle lst ->
        let lst =
          List.map
            (fun (op, xs, c) ->
              match Value.Env.lookup_operation op env with
                | Some k ->
                  let n = List.length xs in
                  if n = k
                  then
                    let bound = List.fold_left (fun bound x -> add_bound x bound) bound xs in
                    op, (xs, comp ~yield:false env bound c)
                  else
                    Error.syntax ~loc "operation %t expects %d arguments but was matched with %d" (Name.print_ident op) k n
                | None -> Error.syntax ~loc "unknown operation %t" (Name.print_ident op)
            )
            lst
        in
        Syntax.TopHandle lst

    | Input.TopLet (x, yts, u, ((_, loc) as c)) ->
      let c = match u with
        | None -> c
        | Some u ->
          Input.Ascribe (c, u), loc in
      let yts = List.map (fun (y, t) -> y, Some t) yts in
      let c = Input.Lambda (yts, c), loc in
      let c = comp ~yield:false env bound c in
      Syntax.TopLet (x, c)

    | Input.TopCheck c ->
      let c = comp ~yield:false env bound c in
      Syntax.TopCheck c

    | Input.Quit -> Syntax.Quit

    | Input.Help -> Syntax.Help

    | Input.Verbosity n -> Syntax.Verbosity n

    | Input.Include (fs, b) -> Syntax.Include (fs, b)

    | Input.Environment -> Syntax.Environment

  in
  d', loc
