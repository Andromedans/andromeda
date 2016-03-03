(** Conversion from sugared to desugared input syntax *)

(** Bound variable management *)
module Bound = struct

  type bound_info =
    | Val of int
    | Const of Name.constant
    | Data of Name.data * int
    | Op of Name.operation * int
    | Sig of Name.signature
    | Dyn of Value.dyn

  type t = { toplevel : (Name.ident * bound_info) list; locals : Name.ident list; depth : int }

  (** Add index information to the bound_info *)
  let compute_indices bound =
    let rec fold acc i = function
      | [] -> List.rev acc
      | (x,Value.BoundVal) :: rem -> fold ((x,Val i)::acc) (i+1) rem
      | (x,Value.BoundConst c) :: rem -> fold ((x,Const c)::acc) i rem
      | (x,Value.BoundData (c,k)) :: rem -> fold ((x,Data (c,k))::acc) i rem
      | (x,Value.BoundOp (op,k)) :: rem -> fold ((x,Op (op,k))::acc) i rem
      | (x,Value.BoundSig s) :: rem -> fold ((x,Sig s)::acc) i rem
      | (x,Value.BoundDyn y) :: rem -> fold ((x,Dyn y)::acc) i rem
    in
    {toplevel = fold [] 0 bound; locals = []; depth = 0}

  let add x bound = {bound with locals = x :: bound.locals; depth = bound.depth + 1}

  let find ~loc x {toplevel;locals;depth} =
    match Name.index_of_ident x locals with
      | Some i -> Val i
      | None ->
        begin match Name.assoc_ident x toplevel with
          | Some (Val k) -> Val (k+depth)
          | Some (Const _ | Data _ | Op _ | Sig _ | Dyn _ as b) -> b
          | None -> Error.syntax ~loc "Unknown name %t." (Name.print_ident x)
        end

  let get_dynamic ~loc x bound =
    match find ~loc x bound with
      | Dyn y -> y
      | Val _ | Const _ | Op _ | Data _ | Sig _ ->
        Error.syntax ~loc "The variable %t is not a dynamic variable." (Name.print_ident x)

  let get_signature ~loc x bound =
    match find ~loc x bound with
      | Sig s -> s
      | Val _ | Const _ | Op _ | Data _ | Dyn _ ->
        Error.syntax ~loc "The variable %t is not a signature." (Name.print_ident x)

  let get_operation ~loc x bound =
    match find ~loc x bound with
      | Op (op,k) -> op,k
      | Val _ | Const _ | Data _ | Sig _ | Dyn _ ->
        Error.syntax ~loc "The name %t is not a operation." (Name.print_ident x)

end

module IdentMap = Name.IdentMap

let mk_lambda ~loc ys c =
  List.fold_left (fun c (y,u) -> Syntax.Lambda (y,u,c), loc) c ys

let mk_prod ~loc ys t =
  List.fold_left (fun c (y,u) -> Syntax.Prod (y,u,c), loc) t ys

(* n is the length of vars *)
let rec tt_pattern bound vars n (p,loc) =
  match p with
    | Input.Tt_Anonymous ->
      (Syntax.Tt_Anonymous, loc), vars, n

    | Input.Tt_As (p,x) ->
      begin match Name.assoc_ident x vars with
        | Some i ->
          let p, vars, n = tt_pattern bound vars n p in
          (Syntax.Tt_As (p,i), loc), vars, n
        | None ->
          let i = n in
          let p, vars, n = tt_pattern bound ((x,n)::vars) (n+1) p in
          (Syntax.Tt_As (p,i), loc), vars, n
      end

    | Input.Tt_Var x ->
      begin match Name.assoc_ident x vars with
        | Some i ->
          (Syntax.Tt_As ((Syntax.Tt_Anonymous, loc), i), loc), vars, n
        | None ->
          (Syntax.Tt_As ((Syntax.Tt_Anonymous, loc), n), loc), ((x,n)::vars), (n+1)
      end

    | Input.Tt_Type ->
      (Syntax.Tt_Type, loc), vars, n

    | Input.Tt_Name x ->
      begin match Bound.find ~loc x bound with
        | Bound.Val k -> (Syntax.Tt_Bound k, loc), vars, n
        | Bound.Const c -> (Syntax.Tt_Constant c, loc), vars, n
        | Bound.Data _ -> Error.syntax ~loc "data constructor in a term pattern"
        | Bound.Op _ -> Error.syntax ~loc "operation in a term pattern"
        | Bound.Sig s -> (Syntax.Tt_Signature s, loc), vars, n
        | Bound.Dyn y -> (Syntax.Tt_Dynamic y, loc), vars, n
      end

    | Input.Tt_Lambda (b,x,popt,p) ->
      let popt, vars, n = match popt with
        | None ->
          None, vars, n
        | Some p ->
          let p, vars, n = tt_pattern bound vars n p in
          Some p, vars, n
        in
      let bopt, vars, n =
        if b
        then
          begin match Name.assoc_ident x vars with
            | Some i ->
            (* XXX it might be a good idea to warn if x is already a pattern variable, since that should never match. *)
              Some i, vars, n
            | None ->
              Some n, ((x,n)::vars), (n+1)
          end
        else None, vars, n
      in
      let p, vars, n = tt_pattern (Bound.add x bound) vars n p in
      (Syntax.Tt_Lambda (x,bopt,popt,p), loc), vars, n

    | Input.Tt_Apply (p1,p2) ->
      let p1, vars, n = tt_pattern bound vars n p1 in
      let p2, vars, n = tt_pattern bound vars n p2 in
      (Syntax.Tt_Apply (p1,p2), loc), vars, n

    | Input.Tt_Prod (b,x,popt,p) ->
      let popt, vars, n = match popt with
        | None ->
          None, vars, n
        | Some p ->
          let p, vars, n = tt_pattern bound vars n p in
          Some p, vars, n
        in
      let bopt, vars, n =
        if b
        then
          begin match Name.assoc_ident x vars with
            | Some i ->
            (* XXX it might be a good idea to warn if x is already a pattern variable, since that should never match. *)
              Some i, vars, n
            | None ->
              Some n, ((x,n)::vars), (n+1)
          end
        else None, vars, n
      in
      let p, vars, n = tt_pattern (Bound.add x bound) vars n p in
      (Syntax.Tt_Prod (x,bopt,popt,p), loc), vars, n

    | Input.Tt_Eq (p1,p2) ->
      let p1, vars, n = tt_pattern bound vars n p1 in
      let p2, vars, n = tt_pattern bound vars n p2 in
      (Syntax.Tt_Eq (p1,p2), loc), vars, n

    | Input.Tt_Refl p ->
      let p, vars, n = tt_pattern bound vars n p in
      (Syntax.Tt_Refl p, loc), vars, n

    | Input.Tt_Structure lps ->
       let rec fold vars n ps = function
        | [] ->
          let ps = List.rev ps in
          (Syntax.Tt_Structure ps, loc), vars, n
        | (l,p)::rem ->
          let p, vars, n = tt_pattern bound vars n p in
          fold vars n ((l,p)::ps) rem
        in
      fold vars n [] lps

    | Input.Tt_Projection (p,l) ->
      let p, vars, n = tt_pattern bound vars n p in
      (Syntax.Tt_Projection (p,l), loc), vars, n

    | Input.Tt_GenSig p ->
      let p,vars,n = pattern bound vars n p in
      (Syntax.Tt_GenSig p, loc), vars, n

    | Input.Tt_GenStruct (p1,p2) ->
      let p1, vars, n = tt_pattern bound vars n p1 in
      let p2, vars, n = pattern bound vars n p2 in
      (Syntax.Tt_GenStruct (p1,p2), loc), vars, n

    | Input.Tt_GenProj (p1,p2) ->
      let p1, vars, n = tt_pattern bound vars n p1 in
      let p2, vars, n = pattern bound vars n p2 in
      (Syntax.Tt_GenProj (p1,p2), loc), vars, n

    | Input.Tt_GenAtom p ->
      let p, vars, n = tt_pattern bound vars n p in
      (Syntax.Tt_GenAtom p, loc), vars, n

    | Input.Tt_GenConstant p ->
      let p, vars, n = tt_pattern bound vars n p in
      (Syntax.Tt_GenConstant p, loc), vars, n

and pattern bound vars n (p,loc) =
  match p with
    | Input.Patt_Anonymous -> (Syntax.Patt_Anonymous, loc), vars, n

    | Input.Patt_As (p,x) ->
      begin match Name.assoc_ident x vars with
        | Some i ->
          let p, vars, n = pattern bound vars n p in
          (Syntax.Patt_As (p,i), loc), vars, n
        | None ->
          let i = n in
          let p, vars, n = pattern bound ((x,i)::vars) (n+1) p in
          (Syntax.Patt_As (p,i), loc), vars, n
      end

    | Input.Patt_Var x ->
      begin match Name.assoc_ident x vars with
        | Some i ->
          (Syntax.Patt_As ((Syntax.Patt_Anonymous, loc), i), loc), vars, n
        | None ->
          (Syntax.Patt_As ((Syntax.Patt_Anonymous, loc), n), loc), ((x,n)::vars), (n+1)
      end

    | Input.Patt_Name x ->
      begin match Bound.find ~loc x bound with
        | Bound.Val k ->
            (Syntax.Patt_Bound k, loc), vars, n
        | Bound.Data (c,k) ->
          if k = 0
          then (Syntax.Patt_Data (c,[]), loc), vars, n
          else Error.syntax ~loc "the data constructor %t expects %d arguments but is matched with 0"
              (Name.print_ident c) k
        | Bound.Const _ | Bound.Op _ | Bound.Sig _ | Bound.Dyn _ ->
          Error.syntax ~loc "cannot match this." (* TODO some can be done *)
      end

    | Input.Patt_Jdg (p1,p2) ->
      let p1, vars, n = tt_pattern bound vars n p1 in
      let p2, vars, n = tt_pattern bound vars n p2 in
      (Syntax.Patt_Jdg (p1,p2), loc), vars, n

    | Input.Patt_Data (t,ps) ->
      begin match Bound.find ~loc t bound with
        | Bound.Data (c,k) ->
          let l = List.length ps in
          if k = l
          then
            let rec fold vars n ps = function
              | [] ->
                let ps = List.rev ps in
                (Syntax.Patt_Data (c,ps), loc), vars, n
              | p::rem ->
                let p, vars, n = pattern bound vars n p in
                fold vars n (p::ps) rem
              in
            fold vars n [] ps
          else
            Error.syntax ~loc "the data constructor %t expects %d arguments but is matched with %d"
                         (Name.print_ident c) k l
        | Bound.Val _ | Bound.Const _ | Bound.Op _ | Bound.Sig _ | Bound.Dyn _ ->
          Error.syntax ~loc "only data constructors can be applied in general patterns"
      end

    | Input.Patt_Cons (p1, p2) ->
      let p1, vars, n = pattern bound vars n p1 in
      let p2, vars, n = pattern bound vars n p2 in
      (Syntax.Patt_Cons (p1,p2), loc), vars, n

    | Input.Patt_List ps ->
       let rec fold ~loc vars n = function
         | [] -> (Syntax.Patt_Nil, loc), vars, n
         | p :: ps ->
            let p, vars, n = pattern bound vars n p in
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
          let p, vars, n = pattern bound vars n p in
          fold vars n (p::ps) rem
        in
      fold vars n [] ps

let rec comp ~yield bound (c',loc) =
  match c' with
    | Input.Handle (c, hcs) ->
       let c = comp ~yield bound c
       and h = handler ~loc bound hcs in
       Syntax.With (h, c), loc

    | Input.With (c1, c2) ->
       let c1 = comp ~yield bound c1
       and c2 = comp ~yield bound c2 in
       Syntax.With (c1, c2), loc

    | Input.Let (lst, c) ->
       let bound, lst = let_clauses ~loc ~yield bound lst in
       let c = comp ~yield bound c in
       Syntax.Let (lst, c), loc

    | Input.LetRec (lst, c) ->
       let bound, lst = letrec_clauses ~loc ~yield bound lst in
       let c = comp ~yield bound c in
       Syntax.LetRec (lst, c), loc

    | Input.Now (x,c1,c2) ->
      let y = Bound.get_dynamic ~loc x bound
      and c1 = comp ~yield bound c1
      and c2 = comp ~yield bound c2 in
      Syntax.Now (y,c1,c2), loc

    | Input.Lookup c ->
       let c = comp ~yield bound c in
       Syntax.Lookup c, loc

    | Input.Ref c ->
       let c = comp ~yield bound c in
       Syntax.Ref c, loc

    | Input.Update (c1, c2) ->
       let c1 = comp ~yield bound c1
       and c2 = comp ~yield bound c2 in
       Syntax.Update (c1, c2), loc

    | Input.Sequence (c1, c2) ->
       let c1 = comp ~yield bound c1
       and c2 = comp ~yield bound c2 in
       Syntax.Sequence (c1, c2), loc

    | Input.Assume ((x, t), c) ->
       let t = comp ~yield bound t in
       let bound = Bound.add x bound in
       let c = comp ~yield bound c in
       Syntax.Assume ((x, t), c), loc

    | Input.Where (c1, c2, c3) ->
       let c1 = comp ~yield bound c1
       and c2 = comp ~yield bound c2
       and c3 = comp ~yield bound c3 in
       Syntax.Where (c1, c2, c3), loc

    | Input.Match (c, cases) ->
       let c = comp ~yield bound c
       and cases = List.map (match_case ~yield bound) cases in
       Syntax.Match (c, cases), loc

    | Input.Ascribe (c, t) ->
       let t = comp ~yield bound t
       and c = comp ~yield bound c in
       Syntax.Ascribe (c, t), loc

    | Input.External s ->
       Syntax.External s, loc

    | Input.Lambda (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let c = comp ~yield bound c in
           mk_lambda ~loc ys c
        | (x, None) :: xs ->
          let bound = Bound.add x bound
          and ys = (x, None) :: ys in
          fold bound ys xs
        | (x, Some t) :: xs ->
          let ys = (let t = comp ~yield bound t in (x, Some t) :: ys)
          and bound = Bound.add x bound in
          fold bound ys xs
      in
      fold bound [] xs

    | Input.Spine (e, cs) ->
      spine ~yield bound e cs

    | Input.Prod (xs, c) ->
      let rec fold bound ys = function
        | [] ->
           let c = comp ~yield bound c in
           mk_prod ~loc ys c
        | (x,t) :: xs ->
          let ys = (let t = comp ~yield bound t in (x, t) :: ys) in
          let bound = Bound.add x bound in
          fold bound ys xs
      in
      fold bound [] xs

    | Input.Eq (c1, c2) ->
      let c1 = comp ~yield bound c1
      and c2 = comp ~yield bound c2 in
      Syntax.Eq (c1, c2), loc

    | Input.Refl c ->
      let c = comp ~yield bound c in
      Syntax.Refl c, loc

    | Input.Signature (s,cs) ->
      let s = Bound.get_signature ~loc s bound in
      let rec fold bound xcs = function
        | [] ->
          Syntax.Signature (s,List.rev xcs), loc
        | (l,mx,mc)::cs ->
          let x = match mx with | Some x -> x | None -> l in
          let mc = match mc with
            | Some c -> Some (comp ~yield bound c)
            | None -> None
          in
          let bound = Bound.add x bound in
          fold bound ((l,x,mc)::xcs) cs
      in
      fold bound [] cs

    | Input.Structure lycs ->
       let rec fold bound res = function
        | [] -> List.rev res
        | (l,x,c) :: rem ->
          let x = match x with | Some x -> x | None -> l in
          let c = match c with | Some c -> Some (comp ~yield bound c) | None -> None in
          fold (Bound.add x bound) ((l,x,c) :: res) rem
        in
      let lcs = fold bound [] lycs in
      Syntax.Structure lcs, loc

    | Input.Projection (c,l) ->
      let c = comp ~yield bound c in
      Syntax.Projection (c,l), loc

    | Input.Var x ->
      begin match Bound.find ~loc x bound with
        | Bound.Val k -> Syntax.Bound k, loc
        | Bound.Const c ->
          Syntax.Constant c, loc

        | Bound.Data (c,k) ->
          if k = 0 then Syntax.Data (c, []), loc
          else Error.syntax ~loc "this data constructor needs %d more arguments" k

        | Bound.Op (op,k) ->
          if k = 0 then Syntax.Operation (op, []), loc
          else Error.syntax ~loc "this operation needs %d more arguments" k

        | Bound.Sig s ->
          Syntax.Signature (s,[]), loc

        | Bound.Dyn y ->
          Syntax.Dynamic y, loc
      end

  | Input.Type ->
    Syntax.Type, loc

  | Input.Yield c ->
    if yield
    then
      let c = comp ~yield bound c in
      Syntax.Yield c, loc
    else
      Error.syntax ~loc "yield may only be used in a handler"

  | Input.Hypotheses ->
     Syntax.Hypotheses, loc

  | Input.Function (xs, c) ->
     let rec fold bound = function
       | [] -> comp ~yield bound c
       | x :: xs ->
          let bound = Bound.add x bound in
          let c = fold bound xs in
          Syntax.Function (x, c), loc
     in
     fold bound xs

  | Input.Handler hcs ->
     handler ~loc bound hcs

  | Input.List cs ->
     let rec fold ~loc = function
       | [] -> Syntax.Nil, loc
       | c :: cs ->
          let c = comp ~yield bound c in
          let cs = fold ~loc:(snd c) cs in
          Syntax.Cons (c, cs), loc
     in
     fold ~loc cs

  | Input.Cons (e1, e2) ->
    let e1 = comp ~yield bound e1 in
    let e2 = comp ~yield bound e2 in
    Syntax.Cons (e1,e2), loc

  | Input.Tuple cs ->
    let lst = List.map (comp ~yield bound) cs in
    Syntax.Tuple lst, loc

  | Input.Congruence (e1,e2) ->
    let e1 = comp ~yield bound e1 in
    let e2 = comp ~yield bound e2 in
    Syntax.Congruence (e1,e2), loc

  | Input.Extensionality (e1,e2) ->
    let e1 = comp ~yield bound e1 in
    let e2 = comp ~yield bound e2 in
    Syntax.Extensionality (e1,e2), loc

  | Input.Reduction c ->
     let c = comp ~yield bound c in
     Syntax.Reduction c, loc

  | Input.String s ->
    Syntax.String s, loc

  | Input.GenSig (c1,c2) ->
    let c1 = comp ~yield bound c1
    and c2 = comp ~yield bound c2 in
    Syntax.GenSig (c1,c2), loc

  | Input.GenStruct (c1,c2) ->
    let c1 = comp ~yield bound c1
    and c2 = comp ~yield bound c2 in
    Syntax.GenStruct (c1,c2), loc

  | Input.GenProj (c1,c2) ->
    let c1 = comp ~yield bound c1
    and c2 = comp ~yield bound c2 in
    Syntax.GenProj (c1,c2), loc

  | Input.Context c ->
    let c = comp ~yield bound c in
    Syntax.Context c, loc

  | Input.Occurs (c1,c2) ->
    let c1 = comp ~yield bound c1
    and c2 = comp ~yield bound c2 in
    Syntax.Occurs (c1,c2), loc

  | Input.Ident x -> Syntax.Ident x, loc

and let_clauses ~loc ~yield bound lst =
  let rec fold bound' lst' = function
    | [] ->
       let lst' = List.rev lst' in
       bound', lst'
    | (x, ys, t_opt, c) :: xcs ->
       if List.exists (fun (y, _, _, _) -> Name.eq_ident x y) xcs
       then
         Error.syntax ~loc "%t is bound more than once" (Name.print_ident x)
       else
         let c = let_clause ~yield bound ys t_opt c in
         let bound' = Bound.add x bound' in
         let lst' = (x, c) :: lst' in
         fold bound' lst' xcs
  in
  fold bound [] lst

and letrec_clauses ~loc ~yield bound lst =
  let bound =
    List.fold_left (fun bound (f, _, _, _, _) -> Bound.add f bound) bound lst
  in
  let rec fold lst' = function
    | [] ->
       let lst' = List.rev lst' in
       bound, lst'
    | (f, y, ys, t_opt, c) :: xcs ->
       if List.exists (fun (g, _, _, _, _) -> Name.eq_ident f g) xcs
       then
         Error.syntax ~loc "%t is bound more than once" (Name.print_ident f)
       else
         let y, c = letrec_clause ~yield bound y ys t_opt c in
         let lst' = (f, y, c) :: lst' in
         fold lst' xcs
  in
  fold [] lst

and let_clause ~yield bound ys t_opt c =
  let rec fold bound = function
    | [] ->
       begin
         match t_opt with
         | None -> comp ~yield bound c
         | Some t ->
            let t = comp ~yield bound t
            and c = comp ~yield bound c in
            Syntax.Ascribe (c, t), (snd c) (* XXX improve location *)
       end
    | y :: ys ->
       let bound = Bound.add y bound in
       let c = fold bound ys in
       Syntax.Function (y, c), (snd c) (* XXX improve location *)
  in
  fold bound ys

and letrec_clause ~yield bound y ys t_opt c =
  let bound = Bound.add y bound in
  let c = let_clause ~yield bound ys t_opt c in
  y, c


(* Desugar a spine. This function is a bit messy because we need to untangle
   to env. But it's worth doing to make users happy. TODO outdated comment *)
and spine ~yield bound ((c',loc) as c) cs =

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
    match c' with
      | Input.Var x ->
        begin match Bound.find ~loc x bound with
          | Bound.Val i -> (Syntax.Bound i, loc), cs
          | Bound.Const x ->
            (Syntax.Constant x, loc), cs
          | Bound.Data (x,k) ->
            let cs', cs = split "data constructor" k cs in
            data ~loc ~yield bound x cs', cs
          | Bound.Op (op,k) ->
            let cs', cs = split "operation" k cs in
            operation ~loc ~yield bound op cs', cs
          | Bound.Sig s ->
            (Syntax.Signature (s,[]),loc), cs
          | Bound.Dyn y ->
            (Syntax.Dynamic y, loc), cs
        end

      | _ -> comp ~yield bound c, cs
  in

  List.fold_left (fun h c ->
    let c = comp ~yield bound c in
    Syntax.Apply (h,c), loc) c cs

(* Desugar handler cases. *)
and handler ~loc bound hcs =
  (* for every case | #op p => c we do #op binder => match binder with | p => c end *)
  let rec fold val_cases op_cases finally_cases = function
    | [] ->
      List.rev val_cases, IdentMap.map List.rev op_cases, List.rev finally_cases

    | Input.CaseVal c :: hcs ->
      (* XXX if this handler is in a outer handler's operation case, should we use its yield?
         eg handle ... with | op => handler | val x => yield x end end *)
      let case = match_case ~yield:false bound c in
      fold (case::val_cases) op_cases finally_cases hcs

    | Input.CaseOp (op, ((ps,_,_) as c)) :: hcs ->
      let op,k = Bound.get_operation ~loc op bound in
      let n = List.length ps in
      if n = k
      then
        let case = match_op_case ~yield:true bound c in
        let my_cases = try IdentMap.find op op_cases with | Not_found -> [] in
        let my_cases = case::my_cases in
        fold val_cases (IdentMap.add op my_cases op_cases) finally_cases hcs
      else
        Error.syntax ~loc "operation %t expects %d arguments but was matched with %d" (Name.print_ident op) k n

    | Input.CaseFinally c :: hcs ->
      let case = match_case ~yield:false bound c in
      fold val_cases op_cases (case::finally_cases) hcs

  in
  let handler_val, handler_ops, handler_finally = fold [] IdentMap.empty [] hcs in
  Syntax.Handler (Syntax.{handler_val; handler_ops; handler_finally}), loc

(* Desugar a match case *)
and match_case ~yield bound (p, c) =
  let p, vars, _ = pattern bound [] 0 p in
  let rec fold xs bound = function
    | [] -> xs, bound
    | (x,_)::rem -> fold (x::xs) (Bound.add x bound) rem
    in
  let xs, bound = fold [] bound vars in
  let c = comp ~yield bound c in
  (xs, p, c)

and match_op_case ~yield bound (ps, pt, c) =
  let rec fold_patterns ps vars n = function
    | [] -> List.rev ps, vars, n
    | p::rem ->
      let p, vars, n = pattern bound vars n p in
      fold_patterns (p::ps) vars n rem
  in
  let ps, vars, n = fold_patterns [] [] 0 ps in
  let pt, vars = match pt with
    | Some p ->
      let p, vars, n = pattern bound vars n p in
      Some p, vars
    | None ->
      None, vars
  in
  let rec fold xs bound = function
    | [] -> xs, bound
    | (x,_)::rem -> fold (x::xs) (Bound.add x bound) rem
    in
  let xs, bound = fold [] bound vars in
  let c = comp ~yield bound c in
  (xs, ps, pt, c)

and data ~loc ~yield bound x cs =
  let cs = List.map (comp ~yield bound) cs in
  Syntax.Data (x, cs), loc

and operation ~loc ~yield bound x cs =
  let cs = List.map (comp ~yield bound) cs in
  Syntax.Operation (x, cs), loc

let toplevel bound (d', loc) =
  let bound = Bound.compute_indices bound in
  let d' = match d' with
    | Input.DeclOperation (x, k) -> Syntax.DeclOperation (x, k)

    | Input.DeclData (x, k) -> Syntax.DeclData (x, k)

    | Input.DeclConstants (xs, u) ->
       let u = comp ~yield:false bound u in
       Syntax.DeclConstants (xs, u)

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
              let c = comp ~yield:false bound c in
              fold (Bound.add y bound) (x::labels) ((x,y,c)::res) rem
       in
       let lst = fold bound [] [] lst in
       Syntax.DeclSignature (s, lst)

    | Input.TopHandle lst ->
        let lst =
          List.map
            (fun (op, (xs, y, c)) ->
              let op,k = Bound.get_operation ~loc op bound in
              let n = List.length xs in
              if n = k
              then
                let bound = List.fold_left (fun bound x -> Bound.add x bound) bound xs in
                let bound = match y with | Some y -> Bound.add y bound | None -> bound in
                op, (xs, y, comp ~yield:false bound c)
              else
                Error.syntax ~loc "operation %t expects %d arguments but was matched with %d"
                             (Name.print_ident op) k n
            )
            lst
        in
        Syntax.TopHandle lst

    | Input.TopLet lst ->
       let bound, lst = let_clauses ~loc ~yield:false bound lst in
       Syntax.TopLet lst

    | Input.TopLetRec lst ->
       let bound, lst = letrec_clauses ~loc ~yield:false bound lst in
       Syntax.TopLetRec lst

    | Input.TopDynamic (x,c) ->
      let c = comp ~yield:false bound c in
      Syntax.TopDynamic (x,c)

    | Input.TopNow (x,c) ->
      let y = Bound.get_dynamic ~loc x bound in
      let c = comp ~yield:false bound c in
      Syntax.TopNow (y,c)

    | Input.TopDo c ->
      let c = comp ~yield:false bound c in
      Syntax.TopDo c

    | Input.TopFail c ->
      let c = lazy (comp ~yield:false bound c) in
      Syntax.TopFail c

    | Input.Quit -> Syntax.Quit

    | Input.Help -> Syntax.Help

    | Input.Verbosity n -> Syntax.Verbosity n

    | Input.Include (fs, b) -> Syntax.Include (fs, b)

    | Input.Environment -> Syntax.Environment

  in
  d', loc

