(** Conversion from sugared to desugared input syntax *)

module IntSet = Set.Make (struct
                    type t = int
                    let compare = compare
                  end)

module IdentMap = Name.IdentMap

let add_bound x bound = x :: bound

let mk_lambda ~loc ys c =
  List.fold_left (fun c (y,u) -> Syntax.Lambda (y,u,c), loc) c ys

let mk_prod ~loc ys t =
  List.fold_left (fun c (y,u) -> Syntax.Prod (y,u,c), loc) t ys

let find_signature ~loc env ls =
  match Value.find_signature env ls with
  | Some s -> s
  | None -> Error.syntax ~loc "unknown structure"


(* n is the length of vars *)
let rec tt_pattern (env : Value.env) bound vars n (p,loc) =
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
             match Value.lookup_decl x env with
             | Some (Value.DeclConstant _) -> (Syntax.Tt_Constant x, loc), vars, n
             | Some (Value.DeclData _) -> Error.syntax ~loc "data in a term pattern"
             | Some (Value.DeclOperation _) -> Error.syntax ~loc "operation in a term pattern"
             | Some (Value.DeclSignature _) -> (Syntax.Tt_Signature x, loc), vars, n
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

    | Input.Tt_Apply (p1,p2) ->
      let p1, vars, n = tt_pattern env bound vars n p1 in
      let p2, vars, n = tt_pattern env bound vars n p2 in
      (Syntax.Tt_Apply (p1,p2), loc), vars, n

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

    | Input.Tt_Structure lps ->
       let s = find_signature ~loc env (List.map fst lps) in
       let rec fold vars n ps = function
        | [] ->
          let ps = List.rev ps in
          (Syntax.Tt_Structure (s, ps), loc), vars, n
        | (_,p)::rem ->
          let p, vars, n = tt_pattern env bound vars n p in
          fold vars n (p::ps) rem
        in
      fold vars n [] lps

    | Input.Tt_Projection (p,l) ->
      let p, vars, n = tt_pattern env bound vars n p in
      (Syntax.Tt_Projection (p,l), loc), vars, n

    | Input.Tt_GenSig x ->
      let i,vars,n = begin match x with
        | Some x ->
          begin try
            let i = List.assoc x vars in
            Some i, vars, n
          with | Not_found ->
            Some n, ((x,n)::vars), (n+1)
          end
        | None -> None, vars, n
        end
      in
      (Syntax.Tt_GenSig i, loc), vars, n

    | Input.Tt_GenStruct (p,x) ->
      let i,vars,n = begin match x with
        | Some x ->
          begin try
            let i = List.assoc x vars in
            Some i, vars, n
          with | Not_found ->
            Some n, ((x,n)::vars), (n+1)
          end
        | None -> None, vars, n
        end
      in
      let p, vars, n = tt_pattern env bound vars n p in
      (Syntax.Tt_GenStruct (p,i), loc), vars, n

    | Input.Tt_GenProj (p,x) ->
      let i,vars,n = begin match x with
        | Some x ->
          begin try
            let i = List.assoc x vars in
            Some i, vars, n
          with | Not_found ->
            Some n, ((x,n)::vars), (n+1)
          end
        | None -> None, vars, n
        end
      in
      let p, vars, n = tt_pattern env bound vars n p in
      (Syntax.Tt_GenProj (p,i), loc), vars, n

    | Input.Tt_GenAtom ->
      (Syntax.Tt_GenAtom, loc), vars, n

let rec pattern (env : Value.env) bound vars n (p,loc) =
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
          begin match Value.lookup_data x env with
            | Some k ->
              if k = 0
              then (Syntax.Patt_Data (x,[]), loc), vars, n
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

    | Input.Patt_Data (t,ps) ->
      begin match Value.lookup_data t env with
        | Some k ->
          let l = List.length ps in
          if k = l
          then
            let rec fold vars n ps = function
              | [] ->
                let ps = List.rev ps in
                (Syntax.Patt_Data (t,ps), loc), vars, n
              | p::rem ->
                let p, vars, n = pattern env bound vars n p in
                fold vars n (p::ps) rem
              in
            fold vars n [] ps
          else
            Error.syntax ~loc "the data constructor %t expects %d arguments but is matched with %d" (Name.print_ident t) k l
        | None -> Error.syntax ~loc "unknown data constructor %t" (Name.print_ident t)
      end

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

    | Input.Patt_Tuple ps ->
      let rec fold vars n ps = function
        | [] ->
          let ps = List.rev ps in
          (Syntax.Patt_Tuple ps, loc), vars, n
        | p::rem ->
          let p, vars, n = pattern env bound vars n p in
          fold vars n (p::ps) rem
        in
      fold vars n [] ps

let rec comp ~yield (env : Value.env) bound (c',loc) =
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

    | Input.Reduction c ->
      let c = comp ~yield env bound c in
      Syntax.Reduction c, loc

    | Input.External s ->
       Syntax.External s, loc

    | Input.Typeof c ->
      let c = comp ~yield env bound c in
      Syntax.Typeof c, loc

    | Input.Lambda (xs, c) ->
      let rec fold bound ys = function
        | [] ->
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

    | Input.Structure lycs ->
       let s = find_signature ~loc env (List.map (fun (l,_,_)->l) lycs) in
       let rec fold bound res = function
        | [] -> List.rev res
        | (x,y,c) :: rem ->
          let y = match y with | Some y -> y | None -> x in
          let c = comp ~yield env bound c in
          fold (add_bound y bound) ((y,c) :: res) rem
        in
      let lcs = fold bound [] lycs in
      Syntax.Structure (s, lcs), loc

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
              match Value.lookup_decl x env with
              | Some (Value.DeclConstant _) ->
                 Syntax.Constant x, loc

              | Some (Value.DeclData k) ->
                 if k = 0 then Syntax.Data (x, []), loc
                 else Error.syntax ~loc "this data constructor needs %d more arguments" k

              | Some (Value.DeclOperation k) ->
                 if k = 0 then Syntax.Operation (x, []), loc
                 else Error.syntax ~loc "this operation needs %d more arguments" k

              | Some (Value.DeclSignature _) ->
                 Syntax.Signature x, loc

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

  | Input.Tuple cs ->
    let lst = List.map (comp ~yield env bound) cs in
    Syntax.Tuple lst, loc

  | Input.Congruence (e1,e2) ->
    let e1 = comp ~yield env bound e1 in
    let e2 = comp ~yield env bound e2 in
    Syntax.Congruence (e1,e2), loc

  | Input.String s ->
    Syntax.String s, loc

  | Input.GenStruct (c1,c2) ->
    let c1 = comp ~yield env bound c1
    and c2 = comp ~yield env bound c2 in
    Syntax.GenStruct (c1,c2), loc

  | Input.GenProj (c1,c2) ->
    let c1 = comp ~yield env bound c1
    and c2 = comp ~yield env bound c2 in
    Syntax.GenProj (c1,c2), loc

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
           match Value.lookup_decl x env with

           | Some (Value.DeclConstant _) ->
              (Syntax.Constant x, loc), cs

           | Some (Value.DeclData k) ->
              let cs', cs = split "data constructor" k cs in
              data ~loc ~yield env bound x cs', cs

           | Some (Value.DeclOperation k) ->
              let cs', cs = split "operation" k cs in
              operation ~loc ~yield env bound x cs', cs

           | Some (Value.DeclSignature _) ->
              (Syntax.Signature x, loc), cs

           | None ->
              Error.syntax ~loc "unknown identifier %t" (Name.print_ident x)
         end

      | _ -> comp ~yield env bound c, cs
    end in

  List.fold_left (fun h c ->
    let c = comp ~yield env bound c in
    Syntax.Apply (h,c), loc) c cs

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

    | Input.CaseOp (op, ((ps,_,_) as c)) :: hcs ->
      begin match Value.lookup_operation op env with
        | Some k ->
          let n = List.length ps in
          if n = k
          then
            let case = match_op_case ~yield:true env bound c in
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

and match_op_case ~yield env bound (ps, pt, c) =
  let rec fold_patterns ps vars n = function
    | [] -> List.rev ps, vars, n
    | p::rem ->
      let p, vars, n = pattern env bound vars n p in
      fold_patterns (p::ps) vars n rem
  in
  let ps, vars, n = fold_patterns [] [] 0 ps in
  let pt, vars = match pt with
    | Some p ->
      let p, vars, n = tt_pattern env bound vars n p in
      Some p, vars
    | None ->
      None, vars
  in
  let rec fold xs bound = function
    | [] -> xs, bound
    | (x,_)::rem -> fold (x::xs) (add_bound x bound) rem
    in
  let xs, bound = fold [] bound vars in
  let c = comp ~yield env bound c in
  (xs, ps, pt, c)

and data ~loc ~yield env bound x cs =
  let cs = List.map (comp ~yield env bound) cs in
  Syntax.Data (x, cs), loc

and operation ~loc ~yield env bound x cs =
  let cs = List.map (comp ~yield env bound) cs in
  Syntax.Operation (x, cs), loc

let toplevel (env : Value.env) bound (d', loc) =
  let d' = match d' with
    | Input.DeclOperation (x, k) -> Syntax.DeclOperation (x, k)

    | Input.DeclData (x, k) -> Syntax.DeclData (x, k)

    | Input.DeclConstant (x, u) ->
       let u = comp ~yield:false env bound u in
       Syntax.DeclConstant (x, u)

    | Input.DeclSignature (s, lst) ->
       let rec fold bound labels res = function
         | [] -> List.rev res
         | (x,y,c)::rem ->
            let y = match y with | Some y -> y | None -> x in
            if List.mem x labels
            then Error.syntax ~loc "field %t appears more than once" (Name.print_ident x)
            else if Name.is_anonymous x
            then Error.syntax ~loc "anonymous field"
            else
              let c = comp ~yield:false env bound c in
              fold (add_bound y bound) (x::labels) ((x,y,c)::res) rem
       in
       let lst = fold bound [] [] lst in
       Syntax.DeclSignature (s, lst)

    | Input.TopHandle lst ->
        let lst =
          List.map
            (fun (op, (xs, y, c)) ->
              match Value.lookup_operation op env with
                | Some k ->
                  let n = List.length xs in
                  if n = k
                  then
                    let bound = List.fold_left (fun bound x -> add_bound x bound) bound xs in
                    let bound = match y with | Some y -> add_bound y bound | None -> bound in
                    op, (xs, y, comp ~yield:false env bound c)
                  else
                    Error.syntax ~loc "operation %t expects %d arguments but was matched with %d"
                                 (Name.print_ident op) k n
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

    | Input.TopDo c ->
      let c = comp ~yield:false env bound c in
      Syntax.TopDo c

    | Input.TopFail c ->
      let c = comp ~yield:false env bound c in
      Syntax.TopFail c

    | Input.Quit -> Syntax.Quit

    | Input.Help -> Syntax.Help

    | Input.Verbosity n -> Syntax.Verbosity n

    | Input.Include (fs, b) -> Syntax.Include (fs, b)

    | Input.Environment -> Syntax.Environment

  in
  d', loc
