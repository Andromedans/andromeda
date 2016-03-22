(** Conversion from sugared to desugared input syntax *)

(** Ctx variable management *)
module Ctx = struct

  (** A let-bound name has lexical scoping and a dynamic-bound name dynamic scoping. *)
  type scoping =
    | Lexical
    | Dynamic

  (** The arity of an operation or a data constructor. *)
  type arity = int

  type unknown = Unknown

  (** Information about names *)
  type 'index info =
    | Variable of 'index * scoping
    | Constant
    | Constructor of arity
    | Operation of arity
    | Signature

  type t = {
      bound : (Name.ident * unknown info) list;
      tydefs : (Name.ident * arity) list;
      files : string list;
    }

  let empty = {
      bound = [];
      tydefs = [];
      files = [];
    }


  let find ~loc x {bound; _} =
    let at_index i = function
      | Variable (Unknown, s) -> Variable (i, s)
      | Constant -> Constant
      | Signature -> Signature
      | Constructor k -> Constructor k
      | Operation k -> Operation k
    in
    let rec search i = function
      | [] -> Error.syntax ~loc "unknown name %t" (Name.print_ident x)
      | (y, info) :: _ when Name.eq_ident y x -> at_index i info
      | (_, Variable _) :: bound -> search (i+1) bound
      | (_, (Constant | Constructor _ | Operation _ | Signature)) :: bound ->
         search i bound
    in
    search 0 bound

  let get_dynamic ~loc x ctx =
    match find ~loc x ctx with
    | Variable (i, Dynamic) -> i
    | Variable (_, Lexical) | Signature | Constant | Operation _ | Constructor _ ->
       Error.syntax ~loc "%t is not a dynamic variable" (Name.print_ident x)

  let check_signature ~loc x ctx =
    match find ~loc x ctx with
    | Signature -> ()
    | Variable _ | Constant | Operation _ | Constructor _ ->
       Error.syntax ~loc "%t is not a signature." (Name.print_ident x)

  let get_operation ~loc x ctx =
    match find ~loc x ctx with
    | Operation k -> k
    | Variable _ | Constant | Constructor _ | Signature ->
       Error.syntax ~loc "%t is not a operation." (Name.print_ident x)

  let add_lexical x ctx =
    { ctx with bound = (x, Variable (Unknown, Lexical)) :: ctx.bound }

  let add_dynamic x ctx =
    { ctx with bound = (x, Variable (Unknown, Dynamic)) :: ctx.bound }

  let add_operation ~loc op k ctx =
    if List.exists (function (op', Operation _) -> Name.eq_ident op op' | _ -> false) ctx.bound
    then
      Error.syntax ~loc "Operation %t is already declared." (Name.print_ident op)
    else
      { ctx with bound = (op, Operation k) :: ctx.bound }

  let add_constructor ~loc c k ctx =
    if List.exists (function (c', Constructor _) -> Name.eq_ident c c' | _ -> false) ctx.bound
    then
      Error.syntax ~loc "Constructor %t is already declared." (Name.print_ident c)
    else
      { ctx with bound = (c, Constructor k) :: ctx.bound }

  let add_signature ~loc s ctx =
    if List.exists (function (s', Signature) -> Name.eq_ident s s' | _ -> false) ctx.bound
    then
      Error.syntax ~loc "Signature %t is already declared." (Name.print_ident s)
    else
      { ctx with bound = (s, Signature) :: ctx.bound }

  let add_constant ~loc c ctx =
    if List.exists (function (c', Constant) -> Name.eq_ident c c' | _ -> false) ctx.bound
    then
      Error.syntax ~loc "Constant %t is already declared." (Name.print_ident c)
    else
      { ctx with bound = (c, Constant) :: ctx.bound }

  (* Add to the contex the fact that [ty] is a type constructor with
     [k] parameters. *)
  let add_tydef t k ctx =
    { ctx with tydefs = List.append ctx.tydefs [(t, k)] }

  (* Get the arity and de Bruijn level of type named [t] and its definition *)
  let get_tydef ~loc t {tydefs=lst; _} =
    let rec find k = function
      | [] -> Error.syntax ~loc "unknown type constructor %t" (Name.print_ident t)
      | (u, arity) :: lst ->
         if Name.eq_ident t u
         then (k, arity)
         else find (k+1) lst
    in
    find 0 lst

  let push_file f ctx =
    { ctx with
      files = (Filename.basename f) :: ctx.files }

  let included f ctx =
    List.mem (Filename.basename f) ctx.files

end (* module Ctx *)

let locate = Location.locate

(* TODO improve locs *)
let mk_lambda ~loc ys c =
  List.fold_left
    (fun c (y,u) -> locate (Syntax.Lambda (y,u,c)) loc)
    c ys

let mk_prod ~loc ys t =
  List.fold_left
    (fun c (y,u) -> locate (Syntax.Prod (y,u,c)) loc)
    t ys

(* n is the length of vars *)
let rec tt_pattern bound vars n (p,loc) =
  match p with
  | Input.Tt_Anonymous ->
     (locate Syntax.Tt_Anonymous loc), vars, n

  | Input.Tt_As (p,x) ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        let p, vars, n = tt_pattern bound vars n p in
        (locate (Syntax.Tt_As (p,i)) loc), vars, n
     | None ->
        let i = n in
        let p, vars, n = tt_pattern bound ((x,n)::vars) (n+1) p in
        (locate (Syntax.Tt_As (p,i)) loc), vars, n
     end

  | Input.Tt_Var x ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        locate (Syntax.Tt_As ((locate Syntax.Tt_Anonymous loc), i)) loc, vars, n
     | None ->
        locate (Syntax.Tt_As ((locate Syntax.Tt_Anonymous loc), n)) loc, ((x,n)::vars), (n+1)
     end

  | Input.Tt_Type ->
     (locate Syntax.Tt_Type loc), vars, n

  | Input.Tt_Name x ->
     begin match Ctx.find ~loc x bound with
     | Ctx.Variable (i,_) -> locate (Syntax.Tt_Bound i) loc, vars, n
     | Ctx.Constant -> locate (Syntax.Tt_Constant x) loc, vars, n
     | Ctx.Constructor _ -> Error.syntax ~loc "data constructor in a term pattern"
     | Ctx.Operation _ -> Error.syntax ~loc "operation in a term pattern"
     | Ctx.Signature -> locate (Syntax.Tt_Signature x) loc, vars, n
     end

  | Input.Tt_Lambda (b, x, popt, p) ->
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
            (* XXX it might be a good idea to warn if x is already
               a pattern variable, since that should never match. *)
            Some i, vars, n
         | None ->
            Some n, ((x,n)::vars), (n+1)
         end
       else None, vars, n
     in
     let p, vars, n = tt_pattern (Ctx.add_lexical x bound) vars n p in
     locate (Syntax.Tt_Lambda (x,bopt,popt,p)) loc, vars, n

  | Input.Tt_Apply (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = tt_pattern bound vars n p2 in
     locate (Syntax.Tt_Apply (p1,p2)) loc, vars, n

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
     let p, vars, n = tt_pattern (Ctx.add_lexical x bound) vars n p in
     locate (Syntax.Tt_Prod (x,bopt,popt,p)) loc, vars, n

  | Input.Tt_Eq (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = tt_pattern bound vars n p2 in
     locate (Syntax.Tt_Eq (p1,p2)) loc, vars, n

  | Input.Tt_Refl p ->
     let p, vars, n = tt_pattern bound vars n p in
     locate (Syntax.Tt_Refl p) loc, vars, n

  | Input.Tt_Structure lps ->
     let rec fold vars n ps = function
       | [] ->
          let ps = List.rev ps in
          locate (Syntax.Tt_Structure ps) loc, vars, n
       | (l,p)::rem ->
          let p, vars, n = tt_pattern bound vars n p in
          fold vars n ((l,p)::ps) rem
     in
     fold vars n [] lps

  | Input.Tt_Projection (p,l) ->
     let p, vars, n = tt_pattern bound vars n p in
     locate (Syntax.Tt_Projection (p,l)) loc, vars, n

  | Input.Tt_GenSig p ->
     let p,vars,n = pattern bound vars n p in
     locate (Syntax.Tt_GenSig p) loc, vars, n

  | Input.Tt_GenStruct (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = pattern bound vars n p2 in
     locate (Syntax.Tt_GenStruct (p1,p2)) loc, vars, n

  | Input.Tt_GenProj (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = pattern bound vars n p2 in
     locate (Syntax.Tt_GenProj (p1,p2)) loc, vars, n

  | Input.Tt_GenAtom p ->
     let p, vars, n = tt_pattern bound vars n p in
     locate (Syntax.Tt_GenAtom p) loc, vars, n

  | Input.Tt_GenConstant p ->
     let p, vars, n = tt_pattern bound vars n p in
     locate (Syntax.Tt_GenConstant p) loc, vars, n

and pattern bound vars n (p,loc) =
  match p with
  | Input.Patt_Anonymous -> locate Syntax.Patt_Anonymous loc, vars, n

  | Input.Patt_As (p,x) ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        let p, vars, n = pattern bound vars n p in
        locate (Syntax.Patt_As (p,i)) loc, vars, n
     | None ->
        let i = n in
        let p, vars, n = pattern bound ((x,i)::vars) (n+1) p in
        locate (Syntax.Patt_As (p,i)) loc, vars, n
     end

  | Input.Patt_Var x ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        locate (Syntax.Patt_As (locate Syntax.Patt_Anonymous loc, i)) loc, vars, n
     | None ->
        locate (Syntax.Patt_As (locate Syntax.Patt_Anonymous loc, n)) loc, ((x,n)::vars), (n+1)
     end

  | Input.Patt_Name x ->
     begin match Ctx.find ~loc x bound with
     | Ctx.Variable (i,_) ->
        locate (Syntax.Patt_Bound i) loc, vars, n
     | Ctx.Constructor k ->
        if k = 0
        then locate (Syntax.Patt_Constructor (x,[])) loc, vars, n
        else Error.syntax ~loc "the data constructor %t expects %d arguments but is matched with 0"
            (Name.print_ident x) k
     | Ctx.Constant ->
        let p = locate (Syntax.Tt_Constant x) loc in
        let pt = locate Syntax.Tt_Anonymous loc in
        locate (Syntax.Patt_Jdg (p, pt)) loc, vars, n
     | Ctx.Signature ->
        let p = locate (Syntax.Tt_Signature x) loc in
        let pt = locate Syntax.Tt_Anonymous loc in
        locate (Syntax.Patt_Jdg (p, pt)) loc, vars, n
     | Ctx.Operation _ ->
        Error.syntax ~loc "Operations are not valid patterns."
     end

  | Input.Patt_Jdg (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = tt_pattern bound vars n p2 in
     locate (Syntax.Patt_Jdg (p1,p2)) loc, vars, n

  | Input.Patt_Constr (c,ps) ->
     begin match Ctx.find ~loc c bound with
     | Ctx.Constructor k ->
        if k = List.length ps
        then
          let rec fold vars n ps = function
            | [] ->
               let ps = List.rev ps in
               locate (Syntax.Patt_Constructor (c,ps)) loc, vars, n
            | p::rem ->
               let p, vars, n = pattern bound vars n p in
               fold vars n (p::ps) rem
          in
          fold vars n [] ps
        else
          Error.syntax ~loc "the data constructor %t expects %d arguments"
            (Name.print_ident c) k
     | Ctx.Variable _ | Ctx.Constant | Ctx.Operation _ | Ctx.Signature ->
        Error.syntax ~loc "only data constructors can be applied in general patterns"
     end

  | Input.Patt_List ps ->
     let rec fold ~loc vars n = function
       | [] -> locate (Syntax.Patt_Constructor (Name.nil, [])) loc, vars, n
       | p :: ps ->
          let p, vars, n = pattern bound vars n p in
          let ps, vars, n = fold ~loc:(p.Location.loc) vars n ps in
          locate (Syntax.Patt_Constructor (Name.cons, [p ; ps])) loc, vars, n
     in
     fold ~loc vars n ps

  | Input.Patt_Tuple ps ->
     let rec fold vars n ps = function
       | [] ->
          let ps = List.rev ps in
          locate (Syntax.Patt_Tuple ps) loc, vars, n
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
     locate (Syntax.With (h, c)) loc

  | Input.With (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.With (c1, c2)) loc

  | Input.Let (lst, c) ->
     let bound, lst = let_clauses ~loc ~yield bound lst in
     let c = comp ~yield bound c in
     locate (Syntax.Let (lst, c)) loc

  | Input.LetRec (lst, c) ->
     let bound, lst = letrec_clauses ~loc ~yield bound lst in
     let c = comp ~yield bound c in
     locate (Syntax.LetRec (lst, c)) loc

  | Input.Now (x,c1,c2) ->
     let y = Ctx.get_dynamic ~loc x bound
     and c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Now (y,c1,c2)) loc

  | Input.Lookup c ->
     let c = comp ~yield bound c in
     locate (Syntax.Lookup c) loc

  | Input.Ref c ->
     let c = comp ~yield bound c in
     locate (Syntax.Ref c) loc

  | Input.Update (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Update (c1, c2)) loc

  | Input.Sequence (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Sequence (c1, c2)) loc

  | Input.Assume ((x, t), c) ->
     let t = comp ~yield bound t in
     let bound = Ctx.add_lexical x bound in
     let c = comp ~yield bound c in
     locate (Syntax.Assume ((x, t), c)) loc

  | Input.Where (c1, c2, c3) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2
     and c3 = comp ~yield bound c3 in
     locate (Syntax.Where (c1, c2, c3)) loc

  | Input.Match (c, cases) ->
     let c = comp ~yield bound c
     and cases = List.map (match_case ~yield bound) cases in
     locate (Syntax.Match (c, cases)) loc

  | Input.Ascribe (c, t) ->
     let t = comp ~yield bound t
     and c = comp ~yield bound c in
     locate (Syntax.Ascribe (c, t)) loc

  | Input.External s ->
     locate (Syntax.External s) loc

  | Input.Lambda (xs, c) ->
     let rec fold bound ys = function
       | [] ->
          let c = comp ~yield bound c in
          mk_lambda ~loc ys c
       | (x, None) :: xs ->
          let bound = Ctx.add_lexical x bound
          and ys = (x, None) :: ys in
          fold bound ys xs
       | (x, Some t) :: xs ->
          let ys = (let t = comp ~yield bound t in (x, Some t) :: ys)
          and bound = Ctx.add_lexical x bound in
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
          let bound = Ctx.add_lexical x bound in
          fold bound ys xs
     in
     fold bound [] xs

  | Input.Eq (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Eq (c1, c2)) loc

  | Input.Refl c ->
     let c = comp ~yield bound c in
     locate (Syntax.Refl c) loc

  | Input.Signature (s,cs) ->
     Ctx.check_signature ~loc s bound ;
     let rec fold bound xcs = function
       | [] ->
          locate (Syntax.Signature (s,List.rev xcs)) loc
       | (l,mx,mc)::cs ->
          let x = match mx with | Some x -> x | None -> l in
          let mc = match mc with
            | Some c -> Some (comp ~yield bound c)
            | None -> None
          in
          let bound = Ctx.add_lexical x bound in
          fold bound ((l,x,mc)::xcs) cs
     in
     fold bound [] cs

  | Input.Structure lycs ->
     let rec fold bound res = function
       | [] -> List.rev res
       | (l,x,c) :: rem ->
          let x = match x with | Some x -> x | None -> l in
          let c = match c with | Some c -> Some (comp ~yield bound c) | None -> None in
          fold (Ctx.add_lexical x bound) ((l,x,c) :: res) rem
     in
     let lcs = fold bound [] lycs in
     locate (Syntax.Structure lcs) loc

  | Input.Projection (c,l) ->
     let c = comp ~yield bound c in
     locate (Syntax.Projection (c,l)) loc

  | Input.Var x ->
     begin match Ctx.find ~loc x bound with
     | Ctx.Variable (i,_) -> locate (Syntax.Bound i) loc
     | Ctx.Constant -> locate (Syntax.Constant x) loc
     | Ctx.Constructor k ->
        if k = 0 then locate (Syntax.Constructor (x, [])) loc
        else Error.syntax ~loc "this data constructor needs %d more arguments" k
     | Ctx.Operation k ->
        if k = 0 then locate (Syntax.Operation (x, [])) loc
        else Error.syntax ~loc "this operation needs %d more arguments" k
     | Ctx.Signature ->
        locate (Syntax.Signature (x, [])) loc
     end

  | Input.Type ->
     locate Syntax.Type loc

  | Input.Yield c ->
     if yield
     then
       let c = comp ~yield bound c in
       locate (Syntax.Yield c) loc
     else
       Error.syntax ~loc "yield may only be used in a handler"

  | Input.Hypotheses ->
     locate Syntax.Hypotheses loc

  | Input.Function (xs, c) ->
     let rec fold bound = function
       | [] -> comp ~yield bound c
       | x :: xs ->
          let bound = Ctx.add_lexical x bound in
          let c = fold bound xs in
          locate (Syntax.Function (x, c)) loc
     in
     fold bound xs

  | Input.Handler hcs ->
     handler ~loc bound hcs

  | Input.List cs ->
     let rec fold ~loc = function
       | [] -> locate (Syntax.Constructor (Name.nil, [])) loc
       | c :: cs ->
          let c = comp ~yield bound c in
          let cs = fold ~loc:(c.Location.loc) cs in
          locate (Syntax.Constructor (Name.cons, [c ; cs])) loc
     in
     fold ~loc cs

  | Input.Tuple cs ->
     let lst = List.map (comp ~yield bound) cs in
     locate (Syntax.Tuple lst) loc

  | Input.Congruence (e1,e2) ->
     let e1 = comp ~yield bound e1 in
     let e2 = comp ~yield bound e2 in
     locate (Syntax.Congruence (e1,e2)) loc

  | Input.Extensionality (e1,e2) ->
     let e1 = comp ~yield bound e1 in
     let e2 = comp ~yield bound e2 in
     locate (Syntax.Extensionality (e1,e2)) loc

  | Input.Reduction c ->
     let c = comp ~yield bound c in
     locate (Syntax.Reduction c) loc

  | Input.String s ->
     locate (Syntax.String s) loc

  | Input.GenSig (c1,c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.GenSig (c1,c2)) loc

  | Input.GenStruct (c1,c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.GenStruct (c1,c2)) loc

  | Input.GenProj (c1,c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.GenProj (c1,c2)) loc

  | Input.Context c ->
     let c = comp ~yield bound c in
     locate (Syntax.Context c) loc

  | Input.Occurs (c1,c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     locate (Syntax.Occurs (c1,c2)) loc

  | Input.Ident x -> locate (Syntax.Ident x) loc

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
         let bound' = Ctx.add_lexical x bound' in
         let lst' = (x, c) :: lst' in
         fold bound' lst' xcs
  in
  fold bound [] lst

and letrec_clauses ~loc ~yield bound lst =
  let bound =
    List.fold_left (fun bound (f, _, _, _, _) -> Ctx.add_lexical f bound) bound lst
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
            locate (Syntax.Ascribe (c, t)) (c.Location.loc) (* XXX improve location *)
       end
    | y :: ys ->
       let bound = Ctx.add_lexical y bound in
       let c = fold bound ys in
       locate (Syntax.Function (y, c)) (c.Location.loc) (* XXX improve location *)
  in
  fold bound ys

and letrec_clause ~yield bound y ys t_opt c =
  let bound = Ctx.add_lexical y bound in
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
       begin match Ctx.find ~loc x bound with
       | Ctx.Variable (i,_) ->
          locate (Syntax.Bound i) loc, cs
       | Ctx.Constant ->
          locate (Syntax.Constant x) loc, cs
       | Ctx.Constructor k ->
          let cs', cs = split "data constructor" k cs in
          data ~loc ~yield bound x cs', cs
       | Ctx.Operation k ->
          let cs', cs = split "operation" k cs in
          operation ~loc ~yield bound x cs', cs
       | Ctx.Signature ->
          locate (Syntax.Signature (x, [])) loc, cs
       end

    | _ -> comp ~yield bound c, cs
  in

  (* TODO improve locs *)
  List.fold_left (fun h c ->
      let c = comp ~yield bound c in
      locate (Syntax.Apply (h,c)) loc) c cs

(* Desugar handler cases. *)
and handler ~loc bound hcs =
  (* for every case | #op p => c we do #op binder => match binder with | p => c end *)
  let rec fold val_cases op_cases finally_cases = function
    | [] ->
       List.rev val_cases, Name.IdentMap.map List.rev op_cases, List.rev finally_cases

    | Input.CaseVal c :: hcs ->
       (* XXX if this handler is in a outer handler's operation case, should we use its yield?
          eg handle ... with | op => handler | val x => yield x end end *)
       let case = match_case ~yield:false bound c in
       fold (case::val_cases) op_cases finally_cases hcs

    | Input.CaseOp (op, ((ps,_,_) as c)) :: hcs ->
       let k = Ctx.get_operation ~loc op bound in
       let n = List.length ps in
       if n = k
       then
         let case = match_op_case ~yield:true bound c in
         let my_cases = try Name.IdentMap.find op op_cases with | Not_found -> [] in
         let my_cases = case::my_cases in
         fold val_cases (Name.IdentMap.add op my_cases op_cases) finally_cases hcs
       else
         Error.syntax ~loc "operation %t expects %d arguments but was matched with %d" (Name.print_ident op) k n

    | Input.CaseFinally c :: hcs ->
       let case = match_case ~yield:false bound c in
       fold val_cases op_cases (case::finally_cases) hcs

  in
  let handler_val, handler_ops, handler_finally = fold [] Name.IdentMap.empty [] hcs in
  locate (Syntax.Handler (Syntax.{ handler_val ; handler_ops ; handler_finally })) loc

(* Desugar a match case *)
and match_case ~yield bound (p, c) =
  let p, vars, _ = pattern bound [] 0 p in
  let rec fold xs bound = function
    | [] -> xs, bound
    | (x,_)::rem -> fold (x::xs) (Ctx.add_lexical x bound) rem
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
    | (x,_)::rem -> fold (x::xs) (Ctx.add_lexical x bound) rem
  in
  let xs, bound = fold [] bound vars in
  let c = comp ~yield bound c in
  (xs, ps, pt, c)

and data ~loc ~yield bound x cs =
  let cs = List.map (comp ~yield bound) cs in
  locate (Syntax.Constructor (x, cs)) loc

and operation ~loc ~yield bound x cs =
  let cs = List.map (comp ~yield bound) cs in
  locate (Syntax.Operation (x, cs)) loc


let mlty ctx params ty =
  (* Get the de Bruijn index of type parameter x *)
  let get_index x =
    let rec find k = function
      | [] -> None
      | y :: ys ->
         if Name.eq_ident x y
         then Some k
         else find (k+1) ys
    in
    find 0 params
  in

  let rec mlty (ty', loc) =
    let ty' =
      begin match ty' with

      | Input.ML_Arrow (ty1, ty2) ->
         let ty1 = mlty ty1
         and ty2 = mlty ty2 in
         Syntax.ML_Arrow (ty1, ty2)

      | Input.ML_Handler (ty1, ty2) ->
         let ty1 = mlty ty1
         and ty2 = mlty ty2 in
         Syntax.ML_Handler (ty1, ty2)

      | Input.ML_Prod tys ->
         let tys = List.map mlty tys in
         Syntax.ML_Prod tys

      | Input.ML_TyApply (x, args) ->
         begin
           match get_index x with
           | Some k ->
              (* It is a type parameter *)
              begin
                match args with
                | [] -> Syntax.ML_Param k
                | _::_ -> Error.syntax ~loc "ML type parameters cannot be applied"
              end
           | None ->
              (* It is a type name *)
              begin
                let (level, arity) = Ctx.get_tydef ~loc x ctx in
                if arity = List.length args
                then
                  let args = List.map mlty args in
                  Syntax.ML_TyApply (level, args)
                else
                  Error.syntax ~loc "ML type %t should be applied to %d argument%s"
                               (Name.print_ident x) arity (if arity = 1 then "" else "s")
              end
         end
      | Input.ML_Judgment -> Syntax.ML_Judgment
      end
    in
    locate ty' loc
  in
  mlty ty

let decl_operation ~loc ctx params args res =
  let args = List.map (mlty ctx params) args
  and res = mlty ctx params res in
  args, res


let mlty_def ~loc ctx outctx params def =
  match def with
  | Input.ML_Alias ty ->
     let ty = mlty ctx params ty in
     outctx, Syntax.ML_Alias ty
  | Input.ML_Sum lst ->
    let rec fold outctx res = function
      | [] -> outctx, Syntax.ML_Sum (List.rev res)
      | (c, args) :: lst ->
        let args = List.map (mlty ctx params) args in
        let outctx = Ctx.add_constructor ~loc c (List.length args) outctx in
        fold outctx ((c, args)::res) lst
    in
    fold outctx [] lst

let mlty_rec_def ~loc ctx params def =
  match def with 
  | Input.ML_Alias ty ->
     let ty = mlty ctx params ty in
     ctx, Syntax.ML_Alias ty
  | Input.ML_Sum lst ->
    let rec fold ctx res = function
      | [] -> ctx, Syntax.ML_Sum (List.rev res)
      | (c, args) :: lst ->
        let args = List.map (mlty ctx params) args in
        let ctx = Ctx.add_constructor ~loc c (List.length args) ctx in
        fold ctx ((c, args)::res) lst
    in
    fold ctx [] lst
  
let mlty_defs ~loc ctx lst =
  let rec fold outctx res = function
    | [] -> outctx, List.rev res
    | (t, (params, def)) :: lst ->
      let outctx = Ctx.add_tydef t (List.length params) outctx in
      let outctx, def = mlty_def ~loc ctx outctx params def in
      fold outctx ((t, (params, def)) :: res) lst
  in
  fold ctx [] lst

let mlty_rec_defs ~loc ctx lst =
  let ctx = List.fold_left (fun ctx (t, (params,_)) -> Ctx.add_tydef t (List.length params) ctx) ctx lst in
  let rec fold ctx defs = function
    | [] -> (ctx, List.rev defs)
    | (t, (params, def)) :: lst ->
       if List.exists (fun (t', _) -> Name.eq_ident t t') lst
       then
         Error.syntax ~loc "%t is declared more than once." (Name.print_ident t)
       else
         let ctx, def = mlty_rec_def ~loc ctx params def in
         fold ctx ((t, (params, def)) :: defs) lst
  in
  fold ctx [] lst

let rec toplevel ~basedir ctx (cmd, loc) =
  match cmd with

    | Input.DeclOperation (op, (params, args, res)) ->
       let args, res = decl_operation ~loc ctx params args res in
       let ctx = Ctx.add_operation ~loc op (List.length args) ctx in
       (ctx, locate (Syntax.DeclOperation (op, (params, args, res))) loc)

    | Input.DefMLType lst ->
       let ctx, lst = mlty_defs ~loc ctx lst in
       (ctx, locate (Syntax.DefMLType lst) loc)

    | Input.DefMLTypeRec lst ->
       let ctx, lst = mlty_rec_defs ~loc ctx lst in
       (ctx, locate (Syntax.DefMLTypeRec lst) loc)

    | Input.DeclConstants (xs, u) ->
       let u = comp ~yield:false ctx u
       and ctx = List.fold_left (fun ctx x -> Ctx.add_constant ~loc x ctx) ctx xs in
       (ctx, locate (Syntax.DeclConstants (xs, u)) loc)

    | Input.DeclSignature (s, lst) ->
       let rec fold ctx labels res = function
         | [] -> List.rev res
         | (x,y,c)::rem ->
            let y = match y with | Some y -> y | None -> x in
            if List.mem x labels
            then Error.syntax ~loc "field %t appears more than once" (Name.print_ident x)
            else if Name.is_anonymous x
            then Error.syntax ~loc "anonymous field"
            else
              let c = comp ~yield:false ctx c in
              fold (Ctx.add_lexical y ctx) (x::labels) ((x,y,c)::res) rem
       in
       let lst = fold ctx [] [] lst in
       let ctx = Ctx.add_signature ~loc s ctx in
       (ctx, locate (Syntax.DeclSignature (s, lst)) loc)

    | Input.TopHandle lst ->
       let lst =
         List.map
           (fun (op, (xs, y, c)) ->
              let k = Ctx.get_operation ~loc op ctx in
              let n = List.length xs in
              if n = k
              then
                let ctx = List.fold_left (fun ctx x -> Ctx.add_lexical x ctx) ctx xs in
                let ctx = match y with | Some y -> Ctx.add_lexical y ctx | None -> ctx in
                op, (xs, y, comp ~yield:false ctx c)
              else
                Error.syntax ~loc "operation %t expects %d arguments but was matched with %d"
                  (Name.print_ident op) k n
           )
           lst
       in
       (ctx, locate (Syntax.TopHandle lst) loc)

    | Input.TopLet lst ->
       let ctx, lst = let_clauses ~loc ~yield:false ctx lst in
       (ctx, locate (Syntax.TopLet lst) loc)

    | Input.TopLetRec lst ->
       let ctx, lst = letrec_clauses ~loc ~yield:false ctx lst in
       (ctx, locate (Syntax.TopLetRec lst) loc)

    | Input.TopDynamic (x,c) ->
       let c = comp ~yield:false ctx c in
       let ctx = Ctx.add_dynamic x ctx in
       (ctx, locate (Syntax.TopDynamic (x,c)) loc)

    | Input.TopNow (x,c) ->
       let y = Ctx.get_dynamic ~loc x ctx in
       let c = comp ~yield:false ctx c in
       (ctx, locate (Syntax.TopNow (y,c)) loc)

    | Input.TopDo c ->
       let c = comp ~yield:false ctx c in
       (ctx, locate (Syntax.TopDo c) loc)

    | Input.TopFail c ->
       let c = lazy (comp ~yield:false ctx c) in
       (ctx, locate (Syntax.TopFail c) loc)

    | Input.Quit ->
       (ctx, locate Syntax.Quit loc)

    | Input.Verbosity n ->
       (ctx, locate (Syntax.Verbosity n) loc)

    | Input.Include fs ->
      let rec fold ctx res = function
        | [] -> (ctx, locate (Syntax.Included (List.rev res)) loc)
        | fn::fs ->
          let fn =
            if Filename.is_relative fn
            then Filename.concat basedir fn
            else fn
          in
          if Ctx.included fn ctx
          then
            fold ctx res fs
          else
            let ctx, cmds = file ctx fn in
            fold ctx ((fn, cmds)::res) fs
      in
      fold ctx [] fs

and file ctx fn =
  if Ctx.included fn ctx
  then
    ctx, []
  else
    let basedir = Filename.dirname fn in
    let ctx = Ctx.push_file fn ctx in
    let cmds = Ulexbuf.parse (Lexer.read_file ?line_limit:None) Parser.file fn in
    let ctx, cmds = List.fold_left (fun (ctx,cmds) cmd ->
        let ctx, cmd = toplevel ~basedir ctx cmd in
        (ctx, cmd::cmds))
      (ctx,[]) cmds
    in
    ctx, List.rev cmds

