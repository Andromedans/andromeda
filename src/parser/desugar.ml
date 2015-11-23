(** Conversion from sugared to desugared input syntax *)

module IntSet = Set.Make (struct
                    type t = int
                    let compare = compare
                  end)

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

let mk_let ~loc w c =
  match w with
  | [] -> c
  | (_::_) as w -> Syntax.Let (w, c), loc

(* n is the length of vars *)
let rec pattern constants bound vars n (p,loc) =
  match p with
    | Input.Patt_Anonymous -> (Syntax.Patt_Anonymous, loc), vars, n

    | Input.Patt_As (p,x) ->
      begin try
        let i = List.assoc x vars in
        let p, vars, n = pattern constants bound vars n p in
        (Syntax.Patt_As (p,i), loc), vars, n
      with | Not_found ->
        let i = n in
        let p, vars, n = pattern constants bound ((x,n)::vars) (n+1) p in
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
          Error.syntax ~loc "unknown value name %t" (Name.print_ident x)
        | Some k ->
            (Syntax.Patt_Bound k, loc), vars, n
      end

    | Input.Patt_Jdg (p1,p2) ->
      let p1, vars, n = tt_pattern constants bound vars n p1 in
      let p2, vars, n = tt_pattern constants bound vars n p2 in
      (Syntax.Patt_Jdg (p1,p2), loc), vars, n

    | Input.Patt_Tag (t,ps) ->
      let rec fold vars n ps = function
        | [] ->
          let ps = List.rev ps in
          (Syntax.Patt_Tag (t,ps), loc), vars, n
        | p::rem ->
          let p, vars, n = pattern constants bound vars n p in
          fold vars n (p::ps) rem
        in
      fold vars n [] ps

and tt_pattern constants bound vars n (p,loc) =
  match p with
    | Input.Tt_Anonymous ->
      (Syntax.Tt_Anonymous, loc), vars, n

    | Input.Tt_As (p,x) ->
      begin try
        let i = List.assoc x vars in
        let p, vars, n = tt_pattern constants bound vars n p in
        (Syntax.Tt_As (p,i), loc), vars, n
      with | Not_found ->
        let i = n in
        let p, vars, n = tt_pattern constants bound ((x,n)::vars) (n+1) p in
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
        | None ->
          if List.mem_assoc x constants
          then
            (Syntax.Tt_Constant x, loc), vars, n
          else
            Error.syntax ~loc "unknown name %t" (Name.print_ident x)
        | Some k ->
          (Syntax.Tt_Bound k, loc), vars, n
      end

    | Input.Tt_Lambda (b,x,popt,p) ->
      let popt, vars, n = match popt with
        | None ->
          None, vars, n
        | Some p ->
          let p, vars, n = tt_pattern constants bound vars n p in
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
      let p, vars, n = tt_pattern constants (add_bound x bound) vars n p in
      (Syntax.Tt_Lambda (x,bopt,popt,p), loc), vars, n

    | Input.Tt_App (p1,p2) ->
      let p1, vars, n = tt_pattern constants bound vars n p1 in
      let p2, vars, n = tt_pattern constants bound vars n p2 in
      (Syntax.Tt_App (p1,p2), loc), vars, n

    | Input.Tt_Prod (b,x,popt,p) ->
      let popt, vars, n = match popt with
        | None ->
          None, vars, n
        | Some p ->
          let p, vars, n = tt_pattern constants bound vars n p in
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
      let p, vars, n = tt_pattern constants (add_bound x bound) vars n p in
      (Syntax.Tt_Prod (x,bopt,popt,p), loc), vars, n

    | Input.Tt_Eq (p1,p2) ->
      let p1, vars, n = tt_pattern constants bound vars n p1 in
      let p2, vars, n = tt_pattern constants bound vars n p2 in
      (Syntax.Tt_Eq (p1,p2), loc), vars, n

    | Input.Tt_Refl p ->
      let p, vars, n = tt_pattern constants bound vars n p in
      (Syntax.Tt_Refl p, loc), vars, n

    | Input.Tt_Inhab ->
      (Syntax.Tt_Inhab, loc), vars, n

    | Input.Tt_Bracket p ->
      let p, vars, n = tt_pattern constants bound vars n p in
      (Syntax.Tt_Bracket p, loc), vars, n

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
          let p, vars, n = tt_pattern constants bound vars n p in
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
          let p, vars, n = tt_pattern constants bound vars n p in
          fold (add_bound x bound) vars n ((l,x,bopt,p)::xps) rem
        in
      fold bound vars n [] xps

    | Input.Tt_Projection (p,l) ->
      let p, vars, n = tt_pattern constants bound vars n p in
      (Syntax.Tt_Projection (p,l), loc), vars, n


let rec comp constants bound (c',loc) =
  match c' with
    | Input.Operation (op, c) ->
      let c = comp constants bound c in
      Syntax.Operation (op, c), loc

    | Input.Handle (c, hcs) ->
       let c = comp constants bound c
       and h = handler ~loc constants bound hcs in
       Syntax.With (h, c), loc

    | Input.With (c1, c2) ->
       let c1 = comp constants bound c1
       and c2 = comp constants bound c2 in
       Syntax.With (c1, c2), loc

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
      Syntax.Let (xcs, c2), loc

    | Input.Assume ((x, t), c) ->
       let t = comp constants bound t in
       let bound = add_bound x bound in
       let c = comp constants bound c in
       Syntax.Assume ((x, t), c), loc

    | Input.Where (c1, c2, c3) ->
       let c1 = comp constants bound c1
       and c2 = comp constants bound c2
       and c3 = comp constants bound c3 in
       Syntax.Where (c1, c2, c3), loc

    | Input.Match (c, cases) ->
       let c = comp constants bound c
       and cases = List.map (case constants bound) cases in
       Syntax.Match (c, cases), loc

    | Input.Beta (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      Syntax.Beta (xscs, c), loc

    | Input.Eta (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      Syntax.Eta (xscs, c), loc

    | Input.Hint (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      Syntax.Hint (xscs, c), loc

    | Input.Inhabit (xscs, c) ->
      let xscs = List.map (fun (xs, c) -> xs, comp constants bound c) xscs in
      let c = comp constants bound c in
      Syntax.Inhabit (xscs, c), loc

    | Input.Unhint (xs, c) ->
      let c = comp constants bound c in
      Syntax.Unhint (xs, c), loc

    | Input.Ascribe (c, t) ->
       let t = comp constants bound t
       and c = comp constants bound c in
       Syntax.Ascribe (c, t), loc

    | Input.Whnf c ->
      let c = comp constants bound c in
      Syntax.Whnf c, loc

    | Input.Snf c ->
      let c = comp constants bound c in
      Syntax.Snf c, loc

    | Input.External s ->
       Syntax.External s, loc

    | Input.Typeof c ->
      let c = comp constants bound c in
      Syntax.Typeof c, loc

    | Input.Lambda (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let ys = List.rev ys in
           let c = comp constants bound c in
           mk_lambda ~loc ys c
        | (x, None) :: xs ->
          let bound = add_bound x bound
          and ys = (x, None) :: ys in
          fold bound ys xs
        | (x, Some t) :: xs ->
          let ys = (let t = comp constants bound t in (x, Some t) :: ys)
          and bound = add_bound x bound in
          fold bound ys xs
      in
      fold bound [] xs

    | Input.Spine (e, cs) ->
      spine constants bound e cs

    | Input.Prod (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let ys = List.rev ys in
           let c = comp constants bound c in
           mk_prod ~loc ys c
        | (x,t) :: xs ->
          let ys = (let t = comp constants bound t in (x, t) :: ys)
          and bound = add_bound x bound in
          fold bound ys xs
      in
      fold bound [] xs

    | Input.Eq (c1, c2) ->
      let c1 = comp constants bound c1
      and c2 = comp constants bound c2 in
      Syntax.Eq (c1, c2), loc

    | Input.Refl c ->
      let c = comp constants bound c in
      Syntax.Refl c, loc

    | Input.Bracket c ->
      let c = comp constants bound c in
      Syntax.Bracket c, loc

    | Input.Inhab ->
      Syntax.Inhab, loc

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
            let c = comp constants bound c in
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
            let c = comp constants bound c in
            fold (add_bound y bound) (x :: labels) ((x,y,c) :: res) rem
        in
      let lst = fold bound [] [] lst in
      Syntax.Structure lst, loc

    | Input.Projection (c,x) ->
      let c = comp constants bound c in
      Syntax.Projection (c,x), loc

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
         | Some k -> Syntax.Bound k, loc
       end

  | Input.Type ->
    Syntax.Type, loc

  | Input.Function (xs, c) ->
     let rec fold bound = function
       | [] -> comp constants bound c
       | x :: xs ->
          let bound = add_bound x bound in
          let c = fold bound xs in
          Syntax.Function (x, c), loc
     in
       fold bound xs

  | Input.Rec (f, xs, c) ->
     let rec fold bound = function
       | [] -> comp constants bound c
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
     handler ~loc constants bound hcs

  | Input.Tag (t, cs) ->
     let cs = List.map (comp constants bound) cs in
     Syntax.Tag (t, cs), loc

(* Desguar a spine. This function is a bit messy because we need to untangle
   to constants. But it's worth doing to make users happy. *)
and spine constants bound ((c',loc) as c) cs =
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
  let c, cs =
    begin
      match c' with
      | Input.Var x when not (List.mem x bound) ->
        begin
          try
            let k = List.assoc x constants in
            let cs', cs = split k cs in
              (* We make a constant from [x] and [cs'] *)
              constant ~loc constants bound x cs', cs
          with Not_found -> comp constants bound c, cs
        end
      | _ -> comp constants bound c, cs
    end in
  (* Process the remaining arguments. *)
  let cs = List.map (comp constants bound) cs in
  Syntax.Spine (c, cs), loc

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

(* Desugar a match case *)
and case constants bound (p, c) =
  let p, vars, _ = pattern constants bound [] 0 p in
  let rec fold xs bound = function
    | [] -> xs, bound
    | (x,_)::rem -> fold (x::xs) (add_bound x bound) rem
    in
  let xs, bound = fold [] bound vars in
  let c = comp constants bound c in
  (xs, p, c)

and constant ~loc constants bound x cs =
  let cs = List.map (comp constants bound) cs in
  Syntax.Constant (x, cs), loc

let toplevel constants bound (d', loc) =
  let d' = match d' with

    | Input.Axiom (x, ryts, u) ->
      let rec fold bound ryts' = function
        | [] ->
          let u = comp constants bound u in
          let ryts' = List.rev ryts' in
          (ryts', u)
        | (reducing, (y, t)) :: ryts ->
          let t = comp constants bound t in
          let bound = add_bound y bound
          and ryts' = (reducing, (y, t)) :: ryts' in
          fold bound ryts' ryts
      in
      let ryts, u = fold bound [] ryts in
      Syntax.Axiom (x, ryts, u)

    | Input.TopHandle lst ->
       let lst = List.map (fun (op, x, c) -> op, (x, comp constants (add_bound x bound) c)) lst in
       Syntax.TopHandle lst

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
