(** Conversion from sugared to desugared input syntax *)

(** Ctx variable management *)
module Ctx = struct

  type scoping =
    | Lexical
    | Dynamic

  type unknown_index = Unknown
  type arity = int

  type 'index info =
    | Variable of 'index * scoping
    | Constant
    | Constructor of arity
    | Operation of arity
    | Signature

  type ty_decl = { level : Syntax.level ;
                   arity : arity }

  type ty_info =
    | TyParam of Syntax.bound
    | TyDecl of ty_decl

  type t = {
    bound : (Name.ident * unknown_index info) list ;
    ty_decls : (Name.ident * ty_decl) list ;
    ty_params : Name.ident list ;
    files : string list ;
  }

  let empty = { bound = [] ; ty_decls = [] ; ty_params = [] ; files = [] }

  let find ~loc x { bound ; _ } =
    let at_index i = function
      | Variable (Unknown, s) -> Variable (i, s)
      | Constant -> Constant
      | Signature -> Signature
      | Constructor k -> Constructor k
      | Operation k -> Operation k in
    let rec fold i = function
      | [] -> Error.syntax ~loc "Unknown name %t" (Name.print_ident x)
      | (y, bi) :: _ when Name.eq_ident y x -> at_index i bi
      | (_, Variable _) :: bound -> fold (i+1) bound
      | (_, (Constant | Constructor _ | Operation _ | Signature)) :: bound -> fold i bound
    in
    fold 0 bound

  let get_dynamic ~loc x ctx =
    match find ~loc x ctx with
    | Variable (k, Dynamic) -> k
    | Variable (_, Lexical) ->
       Error.syntax ~loc "The variable %t is not dynamic." (Name.print_ident x)
    | Signature | Constant | Operation _ | Constructor _ ->
       Error.syntax ~loc "The name %t is not a dynamic variable." (Name.print_ident x)

  let check_signature ~loc x ctx =
    match find ~loc x ctx with
    | Signature -> ()
    | Variable _ | Constant | Operation _ | Constructor _ ->
       Error.syntax ~loc "The name %t is not a signature." (Name.print_ident x)

  let get_operation ~loc x ctx =
    match find ~loc x ctx with
    | Operation k -> k
    | Variable _ | Constant | Constructor _ | Signature ->
       Error.syntax ~loc "The name %t is not a operation." (Name.print_ident x)

  let add_lexical x ctx =
    { ctx with bound = (x, Variable (Unknown, Lexical)) :: ctx.bound }

  let add_dynamic x ctx =
    { ctx with bound = (x, Variable (Unknown, Dynamic)) :: ctx.bound }

  let add_operation op k ctx =
    { ctx with bound = (op, Operation k) :: ctx.bound }

  let add_constructor c k ctx =
    { ctx with bound = (c, Constructor k) :: ctx.bound }

  let add_signature s ctx =
    { ctx with bound = (s, Signature) :: ctx.bound }

  let add_constant c ctx =
    { ctx with bound = (c, Constant) :: ctx.bound }

  let add_params ~loc ps ctx =
    if not (ctx.ty_params = []) then
      Error.impossible ~loc "Type parameters must be added all in one go"
    else
      { ctx with ty_params = ps }

  let add_tydef ty def =

  let find_ty ~loc ty ctx =

    let rec find_param i = function
      | [] -> None
      | x :: params ->
         if Name.eq_ident x ty
         then Some i
         else find_param (i+1) params

    and find_decl = function
      | [] -> None
      | (x, decl) :: _ when Name.eq_ident x ty ->
         Some decl
      | _ :: decls -> find_decl decls
    in

    match find_param 0 ctx.ty_params with
    | Some i -> TyParam i
    | None ->
       begin match find_decl ctx.ty_decls with
       | Some decl -> TyDecl decl
       | None -> Error.syntax ~loc "Unknown type %t" (Name.print_ident ty)
       end

end

module IdentMap = Name.IdentMap

let mark v loc = {Syntax.term=v ; loc}

let push_file f env =
  { env with
    Ctx.files = (Filename.basename f) :: env.Ctx.files }

let included f env =
  List.mem (Filename.basename f) env.Ctx.files

(* TODO improve locs *)
let mk_lambda ~loc ys c =
  List.fold_left (fun c (y,u) -> mark (Syntax.Lambda (y,u,c)) loc) c ys

let mk_prod ~loc ys t =
  List.fold_left (fun c (y,u) -> mark (Syntax.Prod (y,u,c)) loc) t ys

(* n is the length of vars *)
let rec tt_pattern bound vars n (p,loc) =
  match p with
  | Input.Tt_Anonymous ->
     (mark Syntax.Tt_Anonymous loc), vars, n

  | Input.Tt_As (p,x) ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        let p, vars, n = tt_pattern bound vars n p in
        (mark (Syntax.Tt_As (p,i)) loc), vars, n
     | None ->
        let i = n in
        let p, vars, n = tt_pattern bound ((x,n)::vars) (n+1) p in
        (mark (Syntax.Tt_As (p,i)) loc), vars, n
     end

  | Input.Tt_Var x ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        mark (Syntax.Tt_As ((mark Syntax.Tt_Anonymous loc), i)) loc, vars, n
     | None ->
        mark (Syntax.Tt_As ((mark Syntax.Tt_Anonymous loc), n)) loc, ((x,n)::vars), (n+1)
     end

  | Input.Tt_Type ->
     (mark Syntax.Tt_Type loc), vars, n

  | Input.Tt_Name x ->
     begin match Ctx.find ~loc x bound with
     | Ctx.Variable (k,_) -> mark (Syntax.Tt_Bound k) loc, vars, n
     | Ctx.Constant -> mark (Syntax.Tt_Constant x) loc, vars, n
     | Ctx.Constructor _ -> Error.syntax ~loc "data constructor in a term pattern"
     | Ctx.Operation _ -> Error.syntax ~loc "operation in a term pattern"
     | Ctx.Signature -> mark (Syntax.Tt_Signature x) loc, vars, n
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
     let p, vars, n = tt_pattern (Ctx.add_lexical x bound) vars n p in
     mark (Syntax.Tt_Lambda (x,bopt,popt,p)) loc, vars, n

  | Input.Tt_Apply (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = tt_pattern bound vars n p2 in
     mark (Syntax.Tt_Apply (p1,p2)) loc, vars, n

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
     mark (Syntax.Tt_Prod (x,bopt,popt,p)) loc, vars, n

  | Input.Tt_Eq (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = tt_pattern bound vars n p2 in
     mark (Syntax.Tt_Eq (p1,p2)) loc, vars, n

  | Input.Tt_Refl p ->
     let p, vars, n = tt_pattern bound vars n p in
     mark (Syntax.Tt_Refl p) loc, vars, n

  | Input.Tt_Structure lps ->
     let rec fold vars n ps = function
       | [] ->
          let ps = List.rev ps in
          mark (Syntax.Tt_Structure ps) loc, vars, n
       | (l,p)::rem ->
          let p, vars, n = tt_pattern bound vars n p in
          fold vars n ((l,p)::ps) rem
     in
     fold vars n [] lps

  | Input.Tt_Projection (p,l) ->
     let p, vars, n = tt_pattern bound vars n p in
     mark (Syntax.Tt_Projection (p,l)) loc, vars, n

  | Input.Tt_GenSig p ->
     let p,vars,n = pattern bound vars n p in
     mark (Syntax.Tt_GenSig p) loc, vars, n

  | Input.Tt_GenStruct (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = pattern bound vars n p2 in
     mark (Syntax.Tt_GenStruct (p1,p2)) loc, vars, n

  | Input.Tt_GenProj (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = pattern bound vars n p2 in
     mark (Syntax.Tt_GenProj (p1,p2)) loc, vars, n

  | Input.Tt_GenAtom p ->
     let p, vars, n = tt_pattern bound vars n p in
     mark (Syntax.Tt_GenAtom p) loc, vars, n

  | Input.Tt_GenConstant p ->
     let p, vars, n = tt_pattern bound vars n p in
     mark (Syntax.Tt_GenConstant p) loc, vars, n

and pattern bound vars n (p,loc) =
  match p with
  | Input.Patt_Anonymous -> mark Syntax.Patt_Anonymous loc, vars, n

  | Input.Patt_As (p,x) ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        let p, vars, n = pattern bound vars n p in
        mark (Syntax.Patt_As (p,i)) loc, vars, n
     | None ->
        let i = n in
        let p, vars, n = pattern bound ((x,i)::vars) (n+1) p in
        mark (Syntax.Patt_As (p,i)) loc, vars, n
     end

  | Input.Patt_Var x ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        mark (Syntax.Patt_As (mark Syntax.Patt_Anonymous loc, i)) loc, vars, n
     | None ->
        mark (Syntax.Patt_As (mark Syntax.Patt_Anonymous loc, n)) loc, ((x,n)::vars), (n+1)
     end

  | Input.Patt_Name x ->
     begin match Ctx.find ~loc x bound with
     | Ctx.Variable (k,_) ->
        mark (Syntax.Patt_Bound k) loc, vars, n
     | Ctx.Constructor k ->
        if k = 0
        then mark (Syntax.Patt_Constructor (x,[])) loc, vars, n
        else Error.syntax ~loc "the AML constructor %t expects %d arguments but is matched with 0"
            (Name.print_ident x) k
     | Ctx.Constant ->
        let p = mark (Syntax.Tt_Constant x) loc in
        let pt = mark Syntax.Tt_Anonymous loc in
        mark (Syntax.Patt_Jdg (p, pt)) loc, vars, n
     | Ctx.Signature ->
        let p = mark (Syntax.Tt_Signature x) loc in
        let pt = mark Syntax.Tt_Anonymous loc in
        mark (Syntax.Patt_Jdg (p, pt)) loc, vars, n
     | Ctx.Operation _ ->
        Error.syntax ~loc "Operations are not valid patterns."
     end

  | Input.Patt_Jdg (p1,p2) ->
     let p1, vars, n = tt_pattern bound vars n p1 in
     let p2, vars, n = tt_pattern bound vars n p2 in
     mark (Syntax.Patt_Jdg (p1,p2)) loc, vars, n

  | Input.Patt_Constr (c,ps) ->
     begin match Ctx.find ~loc c bound with
     | Ctx.Constructor k ->
        let l = List.length ps in
        if k = l
        then
          let rec fold vars n ps = function
            | [] ->
               let ps = List.rev ps in
               mark (Syntax.Patt_Constructor (c,ps)) loc, vars, n
            | p::rem ->
               let p, vars, n = pattern bound vars n p in
               fold vars n (p::ps) rem
          in
          fold vars n [] ps
        else
          Error.syntax ~loc "the data constructor %t expects %d arguments but is matched with %d"
            (Name.print_ident c) k l
     | Ctx.Variable _ | Ctx.Constant | Ctx.Operation _ | Ctx.Signature ->
        Error.syntax ~loc "only data constructors can be applied in general patterns"
     end

  | Input.Patt_List ps ->
     let rec fold ~loc vars n = function
       | [] -> mark (Syntax.Patt_Constructor (Name.nil, [])) loc, vars, n
       | p :: ps ->
          let p, vars, n = pattern bound vars n p in
          let ps, vars, n = fold ~loc:(p.Syntax.loc) vars n ps in
          mark (Syntax.Patt_Constructor (Name.cons, [p ; ps])) loc, vars, n
     in
     fold ~loc vars n ps

  | Input.Patt_Tuple ps ->
     let rec fold vars n ps = function
       | [] ->
          let ps = List.rev ps in
          mark (Syntax.Patt_Tuple ps) loc, vars, n
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
     mark (Syntax.With (h, c)) loc

  | Input.With (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     mark (Syntax.With (c1, c2)) loc

  | Input.Let (lst, c) ->
     let bound, lst = let_clauses ~loc ~yield bound lst in
     let c = comp ~yield bound c in
     mark (Syntax.Let (lst, c)) loc

  | Input.LetRec (lst, c) ->
     let bound, lst = letrec_clauses ~loc ~yield bound lst in
     let c = comp ~yield bound c in
     mark (Syntax.LetRec (lst, c)) loc

  | Input.Now (x,c1,c2) ->
     let y = Ctx.get_dynamic ~loc x bound
     and c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     mark (Syntax.Now (y,c1,c2)) loc

  | Input.Lookup c ->
     let c = comp ~yield bound c in
     mark (Syntax.Lookup c) loc

  | Input.Ref c ->
     let c = comp ~yield bound c in
     mark (Syntax.Ref c) loc

  | Input.Update (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     mark (Syntax.Update (c1, c2)) loc

  | Input.Sequence (c1, c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     mark (Syntax.Sequence (c1, c2)) loc

  | Input.Assume ((x, t), c) ->
     let t = comp ~yield bound t in
     let bound = Ctx.add_lexical x bound in
     let c = comp ~yield bound c in
     mark (Syntax.Assume ((x, t), c)) loc

  | Input.Where (c1, c2, c3) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2
     and c3 = comp ~yield bound c3 in
     mark (Syntax.Where (c1, c2, c3)) loc

  | Input.Match (c, cases) ->
     let c = comp ~yield bound c
     and cases = List.map (match_case ~yield bound) cases in
     mark (Syntax.Match (c, cases)) loc

  | Input.Ascribe (c, t) ->
     let t = comp ~yield bound t
     and c = comp ~yield bound c in
     mark (Syntax.Ascribe (c, t)) loc

  | Input.External s ->
     mark (Syntax.External s) loc

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
     mark (Syntax.Eq (c1, c2)) loc

  | Input.Refl c ->
     let c = comp ~yield bound c in
     mark (Syntax.Refl c) loc

  | Input.Signature (s,cs) ->
     Ctx.check_signature ~loc s bound ;
     let rec fold bound xcs = function
       | [] ->
          mark (Syntax.Signature (s,List.rev xcs)) loc
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
     mark (Syntax.Structure lcs) loc

  | Input.Projection (c,l) ->
     let c = comp ~yield bound c in
     mark (Syntax.Projection (c,l)) loc

  | Input.Var x ->
     begin match Ctx.find ~loc x bound with
     | Ctx.Variable (k,_) -> mark (Syntax.Bound k) loc
     | Ctx.Constant ->
        mark (Syntax.Constant x) loc

     | Ctx.Constructor k ->
        if k = 0 then mark (Syntax.Constructor (x, [])) loc
        else Error.syntax ~loc "this data constructor needs %d more arguments" k

     | Ctx.Operation k ->
        if k = 0 then mark (Syntax.Operation (x, [])) loc
        else Error.syntax ~loc "this operation needs %d more arguments" k

     | Ctx.Signature ->
        mark (Syntax.Signature (x, [])) loc
     end

  | Input.Type ->
     mark Syntax.Type loc

  | Input.Yield c ->
     if yield
     then
       let c = comp ~yield bound c in
       mark (Syntax.Yield c) loc
     else
       Error.syntax ~loc "yield may only be used in a handler"

  | Input.Hypotheses ->
     mark Syntax.Hypotheses loc

  | Input.Function (xs, c) ->
     let rec fold bound = function
       | [] -> comp ~yield bound c
       | x :: xs ->
          let bound = Ctx.add_lexical x bound in
          let c = fold bound xs in
          mark (Syntax.Function (x, c)) loc
     in
     fold bound xs

  | Input.Handler hcs ->
     handler ~loc bound hcs

  | Input.List cs ->
     let rec fold ~loc = function
       | [] -> mark (Syntax.Constructor (Name.nil, [])) loc
       | c :: cs ->
          let c = comp ~yield bound c in
          let cs = fold ~loc:(c.Syntax.loc) cs in
          mark (Syntax.Constructor (Name.cons, [c ; cs])) loc
     in
     fold ~loc cs

  | Input.Tuple cs ->
     let lst = List.map (comp ~yield bound) cs in
     mark (Syntax.Tuple lst) loc

  | Input.Congruence (e1,e2) ->
     let e1 = comp ~yield bound e1 in
     let e2 = comp ~yield bound e2 in
     mark (Syntax.Congruence (e1,e2)) loc

  | Input.Extensionality (e1,e2) ->
     let e1 = comp ~yield bound e1 in
     let e2 = comp ~yield bound e2 in
     mark (Syntax.Extensionality (e1,e2)) loc

  | Input.Reduction c ->
     let c = comp ~yield bound c in
     mark (Syntax.Reduction c) loc

  | Input.String s ->
     mark (Syntax.String s) loc

  | Input.GenSig (c1,c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     mark (Syntax.GenSig (c1,c2)) loc

  | Input.GenStruct (c1,c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     mark (Syntax.GenStruct (c1,c2)) loc

  | Input.GenProj (c1,c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     mark (Syntax.GenProj (c1,c2)) loc

  | Input.Context c ->
     let c = comp ~yield bound c in
     mark (Syntax.Context c) loc

  | Input.Occurs (c1,c2) ->
     let c1 = comp ~yield bound c1
     and c2 = comp ~yield bound c2 in
     mark (Syntax.Occurs (c1,c2)) loc

  | Input.Ident x -> mark (Syntax.Ident x) loc

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
            mark (Syntax.Ascribe (c, t)) (c.Syntax.loc) (* XXX improve location *)
       end
    | y :: ys ->
       let bound = Ctx.add_lexical y bound in
       let c = fold bound ys in
       mark (Syntax.Function (y, c)) (c.Syntax.loc) (* XXX improve location *)
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
          mark (Syntax.Bound i) loc, cs
       | Ctx.Constant ->
          mark (Syntax.Constant x) loc, cs
       | Ctx.Constructor k ->
          let cs', cs = split "data constructor" k cs in
          data ~loc ~yield bound x cs', cs
       | Ctx.Operation k ->
          let cs', cs = split "operation" k cs in
          operation ~loc ~yield bound x cs', cs
       | Ctx.Signature ->
          mark (Syntax.Signature (x, [])) loc, cs
       end

    | _ -> comp ~yield bound c, cs
  in

  (* TODO improve locs *)
  List.fold_left (fun h c ->
      let c = comp ~yield bound c in
      mark (Syntax.Apply (h,c)) loc) c cs

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
       let k = Ctx.get_operation ~loc op bound in
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
  mark (Syntax.Handler (Syntax.{ handler_val ; handler_ops ; handler_finally })) loc

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
  mark (Syntax.Constructor (x, cs)) loc

and operation ~loc ~yield bound x cs =
  let cs = List.map (comp ~yield bound) cs in
  mark (Syntax.Operation (x, cs)) loc


let rec aml_ty ctx (ty, loc) =
  let ty =
    match ty with
    | Input.AML_Arrow (dom, cod) ->
       let dom = aml_ty ctx dom
       and cod = aml_ty ctx cod in
       Syntax.AML_Arrow (dom, cod)
    | Input.AML_Handler (dom, cod) ->
       let dom = aml_ty ctx dom
       and cod = aml_ty ctx cod in
       Syntax.AML_Handler (dom, cod)
    | Input.AML_Prod tys ->
       let tys = List.map (aml_ty ctx) tys in
       Syntax.AML_Prod tys
    | Input.AML_TyApply (x, args) ->
       begin match Ctx.find_ty ~loc x ctx with
       | Ctx.TyDecl ({Ctx.level; Ctx.arity}) ->
          let n_args = List.length args in
          if not (n_args = arity) then
            Error.syntax ~loc
              "AML type %t expects %d argument%s but is applied to %d argument%s"
              (Name.print_ident x) arity (if arity = 1 then "" else "s")
              n_args (if n_args = 1 then "" else "s")
          else
            let args = List.map (aml_ty ctx) args in
            Syntax.AML_TyApply (level, args)
       | Ctx.TyParam index ->
          if not (List.length args = 0) then
            Error.syntax ~loc "AML type parameters may not be applied"
          else
            Syntax.AML_Param index
       end
    | Input.AML_Judgment -> Syntax.AML_Judgment
  in
  mark ty loc

let decl_operation ~loc ctx params args res =
  let ctx = Ctx.add_params ~loc params ctx in
  let args = List.map (aml_ty ctx) args
  and res = aml_ty ctx res in
  args, res


(* mltype foo a b = Bob : a -> b -> foo a b | Alice : b -> a -> foo a b *)
(* and    bar c   = Eve *)

let decl_aml_type ~loc ctx lst =
  let lst =
    List.map (fun (ty, aml_def) -> ty, aml_tydef ctx aml_def) lst in
  List.fold_left
    (fun ctx (ty, (params, _)) -> Ctx. )

let decl_aml_type_rec lst = assert false


let toplevel ctx (d', loc) =
  let d' = match d' with
    | Input.DeclOperation (op, (params, args, res)) ->
       let args, res = decl_operation ~loc ctx params args res in
       let ctx = Ctx.add_operation op (List.length args) in
       ctx, [Syntax.DeclOperation (op, params, args, res)]

    | Input.DeclAMLType lst -> decl_aml_type lst

    | Input.DeclAMLTypeRec lst -> decl_aml_type_rec lst

    | Input.DeclConstants (xs, u) ->
       let u = comp ~yield:false ctx u in
       Syntax.DeclConstants (xs, u)

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
       Syntax.DeclSignature (s, lst)

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
       Syntax.TopHandle lst

    | Input.TopLet lst ->
       let ctx, lst = let_clauses ~loc ~yield:false ctx lst in
       Syntax.TopLet lst

    | Input.TopLetRec lst ->
       let ctx, lst = letrec_clauses ~loc ~yield:false ctx lst in
       Syntax.TopLetRec lst

    | Input.TopDynamic (x,c) ->
       let c = comp ~yield:false ctx c in
       Syntax.TopDynamic (x,c)

    | Input.TopNow (x,c) ->
       let y = Ctx.get_dynamic ~loc x ctx in
       let c = comp ~yield:false ctx c in
       Syntax.TopNow (y,c)

    | Input.TopDo c ->
       let c = comp ~yield:false ctx c in
       Syntax.TopDo c

    | Input.TopFail c ->
       let c = lazy (comp ~yield:false ctx c) in
       Syntax.TopFail c

    | Input.Quit -> Syntax.Quit

    | Input.Help -> Syntax.Help

    | Input.Verbosity n -> Syntax.Verbosity n

    | Input.Include (fs, b) -> assert false (* TODO *)

    | Input.Environment -> Syntax.Environment

  in
  d', loc
