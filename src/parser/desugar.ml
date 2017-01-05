(** Conversion from sugared to desugared input syntax *)

(** The arity of an operation or a data constructor. *)
type arity = int

type unknown = Unknown

(** Information about names *)
type 'index info =
  | Variable of 'index
  | Constant
  | Constructor of arity
  | Operation of arity

let print_info info ppf = match info with
  | Variable _ -> Format.fprintf ppf "a variable"
  | Constant -> Format.fprintf ppf "a constant"
  | Constructor _ -> Format.fprintf ppf "an AML constructor"
  | Operation _ -> Format.fprintf ppf "an operation"

type error =
  | UnknownName of Name.ident
  | UnknownTypeName of Name.ident
  | OperationExpected : Name.ident * 'a info -> error
  | ConstantAlreadyDeclared of Name.ident
  | OperationAlreadyDeclared of Name.ident
  | ConstructorAlreadyDeclared of Name.ident
  | InvalidTermPatternName : Name.ident * 'a info -> error
  | InvalidPatternName : Name.ident * 'a info -> error
  | InvalidAppliedPatternName : Name.ident * 'a info -> error
  | ArityMismatch of Name.ident * int * int
  | UnboundYield
  | ParallelShadowing of Name.ident
  | AppliedTyParam

let print_error err ppf = match err with
  | UnknownName x -> Format.fprintf ppf "Unknown name %t." (Name.print_ident x)
  | UnknownTypeName x -> Format.fprintf ppf "Unknown type name %t." (Name.print_ident x)
  | OperationExpected (x, info) -> Format.fprintf ppf "%t should be an operation, but is %t." (Name.print_ident x) (print_info info)
  | ConstantAlreadyDeclared x -> Format.fprintf ppf "A constant %t is already declared." (Name.print_ident x)
  | OperationAlreadyDeclared x -> Format.fprintf ppf "An operation %t is already declared." (Name.print_ident x)
  | ConstructorAlreadyDeclared x -> Format.fprintf ppf "An AML constructor %t is already declared." (Name.print_ident x)
  | InvalidTermPatternName (x, info) -> Format.fprintf ppf "%t cannot be used in a term pattern as it is %t." (Name.print_ident x) (print_info info)
  | InvalidPatternName (x, info) -> Format.fprintf ppf "%t cannot be used in a pattern as it is %t." (Name.print_ident x) (print_info info)
  | InvalidAppliedPatternName (x, info) -> Format.fprintf ppf "%t cannot be applied in a pattern as it is %t." (Name.print_ident x) (print_info info)
  | ArityMismatch (x, used, expected) -> Format.fprintf ppf "%t expects %d arguments but is used with %d." (Name.print_ident x) expected used
  | UnboundYield -> Format.fprintf ppf "yield may only appear in a handler's operation cases."
  | ParallelShadowing x -> Format.fprintf ppf "%t is bound more than once." (Name.print_ident x)
  | AppliedTyParam -> Format.fprintf ppf "AML type parameters cannot be applied."

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

(** Ctx variable management *)
module Ctx = struct

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
      | Variable Unknown -> Variable i
      | Constant -> Constant
      | Constructor k -> Constructor k
      | Operation k -> Operation k
    in
    let rec search i = function
      | [] -> error ~loc (UnknownName x)
      | (y, info) :: _ when Name.eq_ident y x -> at_index i info
      | (_, Variable _) :: bound -> search (i+1) bound
      | (_, (Constant | Constructor _ | Operation _)) :: bound ->
         search i bound
    in
    search 0 bound

  let get_operation ~loc x ctx =
    match find ~loc x ctx with
    | Operation k -> k
    | Variable _ | Constant | Constructor _ as info ->
      error ~loc (OperationExpected (x, info))

  let add_variable x ctx =
    { ctx with bound = (x, Variable Unknown) :: ctx.bound }

  let add_operation ~loc op k ctx =
    if List.exists (function (op', Operation _) -> Name.eq_ident op op' | _ -> false) ctx.bound
    then
      error ~loc (OperationAlreadyDeclared op)
    else
      { ctx with bound = (op, Operation k) :: ctx.bound }

  let add_constructor ~loc c k ctx =
    if List.exists (function (c', Constructor _) -> Name.eq_ident c c' | _ -> false) ctx.bound
    then
      error ~loc (ConstructorAlreadyDeclared c)
    else
      { ctx with bound = (c, Constructor k) :: ctx.bound }

  let add_constant ~loc c ctx =
    if List.exists (function (c', Constant) -> Name.eq_ident c c' | _ -> false) ctx.bound
    then
      error ~loc (ConstantAlreadyDeclared c)
    else
      { ctx with bound = (c, Constant) :: ctx.bound }

  (* Add to the context the fact that [ty] is a type constructor with
     [k] parameters. *)
  let add_tydef t k ctx =
    { ctx with tydefs = List.append ctx.tydefs [(t, k)] }

  (* Get the arity and de Bruijn level of type named [t] and its definition *)
  let get_tydef ~loc t {tydefs=lst; _} =
    let rec find k = function
      | [] -> error ~loc (UnknownTypeName t)
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

let mlty ctx params ty =
  let rec mlty ({Location.thing=ty';loc}) =
    let ty' =
      begin match ty' with

      | Input.ML_Arrow (ty1, ty2) ->
         let ty1 = mlty ty1
         and ty2 = mlty ty2 in
         Dsyntax.ML_Arrow (ty1, ty2)

      | Input.ML_Handler (ty1, ty2) ->
         let ty1 = mlty ty1
         and ty2 = mlty ty2 in
         Dsyntax.ML_Handler (ty1, ty2)

      | Input.ML_Ref t ->
         let t = mlty t in
         Dsyntax.ML_Ref t

      | Input.ML_Dynamic t ->
         let t = mlty t in
         Dsyntax.ML_Dynamic t

      | Input.ML_Prod tys ->
         let tys = List.map mlty tys in
         Dsyntax.ML_Prod tys

      | Input.ML_TyApply (x, args) ->
         begin
           match Name.index_of_ident x params with
           | Some k ->
              (* It is a type parameter *)
              begin
                match args with
                | [] -> Dsyntax.ML_Bound k
                | _::_ -> error ~loc AppliedTyParam
              end
           | None ->
              (* It is a type name *)
              begin
                let (level, arity) = Ctx.get_tydef ~loc x ctx in
                let n = List.length args in
                if arity = n
                then
                  let args = List.map mlty args in
                  Dsyntax.ML_TyApply (x, level, args)
                else
                  error ~loc (ArityMismatch (x, n, arity))
              end
         end

      | Input.ML_Anonymous ->
         Dsyntax.ML_Anonymous

      | Input.ML_Judgment -> Dsyntax.ML_Judgment

      | Input.ML_String -> Dsyntax.ML_String
      end
    in
    locate ty' loc
  in
  mlty ty

(* TODO improve locs *)
let mk_lambda ~loc ys c =
  List.fold_left
    (fun c (y,u) -> locate (Dsyntax.Lambda (y,u,c)) loc)
    c ys

let mk_prod ~loc ys t =
  List.fold_left
    (fun c (y,u) -> locate (Dsyntax.Prod (y,u,c)) loc)
    t ys

(* n is the length of vars *)
let rec tt_pattern ctx vars n {Location.thing=p;loc} =
  match p with
  | Input.Tt_Anonymous ->
     (locate Pattern.Tt_Anonymous loc), vars, n

  | Input.Tt_As (p,x) ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        let p, vars, n = tt_pattern ctx vars n p in
        (locate (Pattern.Tt_As (p,i)) loc), vars, n
     | None ->
        let i = n in
        let p, vars, n = tt_pattern ctx ((x,n)::vars) (n+1) p in
        (locate (Pattern.Tt_As (p,i)) loc), vars, n
     end

  | Input.Tt_Var x ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        locate (Pattern.Tt_As ((locate Pattern.Tt_Anonymous loc), i)) loc, vars, n
     | None ->
        locate (Pattern.Tt_As ((locate Pattern.Tt_Anonymous loc), n)) loc, ((x,n)::vars), (n+1)
     end

  | Input.Tt_Type ->
     (locate Pattern.Tt_Type loc), vars, n

  | Input.Tt_Name x ->
     begin match Ctx.find ~loc x ctx with
     | Variable i -> locate (Pattern.Tt_Bound i) loc, vars, n
     | Constant -> locate (Pattern.Tt_Constant x) loc, vars, n
     | Constructor _ | Operation _ as info -> error ~loc (InvalidTermPatternName (x, info))
     end

  | Input.Tt_Lambda (lst, p) ->
     let rec fold ctx vars n = function
       | [] -> tt_pattern ctx vars n p
       | (x, popt) :: lst ->
          let popt, vars, n = match popt with
            | None -> None, vars, n
            | Some p ->
               let p, vars, n = tt_pattern ctx vars n p in
               Some p, vars, n
          in
          let x, bopt, vars, n =
            begin
              match x with
              | Input.PattVar x ->
                 begin
                   match Name.assoc_ident x vars with
                   | Some i -> x, Some i, vars, n (* previously seen pattern variable *)
                             (* XXX it might be a good idea to warn if x is already
                             a pattern variable, since that should never match. *)
                   | None -> x, Some n, ((x,n)::vars), (n+1) (* new pattern variable *)
                 end
              | Input.NonPattVar x -> x, None, vars, n
            end
          in
          let ctx = Ctx.add_variable x ctx in
          let p, vars, n = fold ctx vars n lst in
          locate (Pattern.Tt_Lambda (x,bopt,popt,p)) loc, vars, n
     in
     fold ctx vars n lst

  | Input.Tt_Spine (p, ps) ->
     let rec fold p vars n = function
       | [] -> p, vars, n
       | q :: lst ->
          let q, vars, n = tt_pattern ctx vars n q in
          let p = locate (Pattern.Tt_Apply (p, q)) loc in
          fold p vars n lst
     in
     let p, vars, n = tt_pattern ctx vars n p in
     fold p vars n ps

  | Input.Tt_Prod (lst, p) ->
     let rec fold ctx vars n = function
       | [] -> tt_pattern ctx vars n p
       | (x, popt) :: lst ->
          let popt, vars, n = match popt with
            | None -> None, vars, n
            | Some p ->
               let p, vars, n = tt_pattern ctx vars n p in
               Some p, vars, n
          in
          let x, bopt, vars, n =
            begin
              match x with
              | Input.PattVar x ->
                 begin
                   match Name.assoc_ident x vars with
                   | Some i -> x, Some i, vars, n (* previously seen pattern variable *)
                             (* XXX it might be a good idea to warn if x is already
                             a pattern variable, since that should never match. *)
                   | None -> x, Some n, ((x,n)::vars), (n+1) (* new pattern variable *)
                 end
              | Input.NonPattVar x -> x, None, vars, n
            end
          in
          let ctx = Ctx.add_variable x ctx in
          let p, vars, n = fold ctx vars n lst in
          locate (Pattern.Tt_Prod (x,bopt,popt,p)) loc, vars, n
     in
     fold ctx vars n lst

  | Input.Tt_Eq (p1,p2) ->
     let p1, vars, n = tt_pattern ctx vars n p1 in
     let p2, vars, n = tt_pattern ctx vars n p2 in
     locate (Pattern.Tt_Eq (p1,p2)) loc, vars, n

  | Input.Tt_Refl p ->
     let p, vars, n = tt_pattern ctx vars n p in
     locate (Pattern.Tt_Refl p) loc, vars, n

  | Input.Tt_GenAtom p ->
     let p, vars, n = tt_pattern ctx vars n p in
     locate (Pattern.Tt_GenAtom p) loc, vars, n

  | Input.Tt_GenConstant p ->
     let p, vars, n = tt_pattern ctx vars n p in
     locate (Pattern.Tt_GenConstant p) loc, vars, n

and pattern ctx vars n {Location.thing=p; loc} =
  match p with
  | Input.Patt_Anonymous -> locate Pattern.Patt_Anonymous loc, vars, n

  | Input.Patt_As (p,x) ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        let p, vars, n = pattern ctx vars n p in
        locate (Pattern.Patt_As (p,i)) loc, vars, n
     | None ->
        let i = n in
        let p, vars, n = pattern ctx ((x,i)::vars) (n+1) p in
        locate (Pattern.Patt_As (p,i)) loc, vars, n
     end

  | Input.Patt_Var x ->
     begin match Name.assoc_ident x vars with
     | Some i ->
        locate (Pattern.Patt_As (locate Pattern.Patt_Anonymous loc, i)) loc, vars, n
     | None ->
        locate (Pattern.Patt_As (locate Pattern.Patt_Anonymous loc, n)) loc, ((x,n)::vars), (n+1)
     end

  | Input.Patt_Name x ->
     begin match Ctx.find ~loc x ctx with
     | Variable i ->
        locate (Pattern.Patt_Bound i) loc, vars, n
     | Constructor k ->
        if k = 0
        then locate (Pattern.Patt_Constructor (x,[])) loc, vars, n
        else error ~loc (ArityMismatch (x, 0, k))
     | Constant ->
        let p = locate (Pattern.Tt_Constant x) loc in
        let pt = locate Pattern.Tt_Anonymous loc in
        locate (Pattern.Patt_Jdg (p, pt)) loc, vars, n
     | Operation _ as info -> error ~loc (InvalidPatternName (x, info))
     end

  | Input.Patt_Jdg (p1, Some p2) ->
     let p1, vars, n = tt_pattern ctx vars n p1 in
     let p2, vars, n = tt_pattern ctx vars n p2 in
     locate (Pattern.Patt_Jdg (p1,p2)) loc, vars, n

  | Input.Patt_Jdg (p1, None) ->
     let p1, vars, n = tt_pattern ctx vars n p1
     and p2 = Location.locate (Pattern.Tt_Anonymous) Location.unknown in
     locate (Pattern.Patt_Jdg (p1, p2)) loc, vars, n

  | Input.Patt_Constr (c,ps) ->
     begin match Ctx.find ~loc c ctx with
     | Constructor k ->
        let len = List.length ps in
        if k = len
        then
          let rec fold vars n ps = function
            | [] ->
               let ps = List.rev ps in
               locate (Pattern.Patt_Constructor (c,ps)) loc, vars, n
            | p::rem ->
               let p, vars, n = pattern ctx vars n p in
               fold vars n (p::ps) rem
          in
          fold vars n [] ps
        else
          error ~loc (ArityMismatch (c, n, k))
     | Variable _ | Constant | Operation _ as info ->
        error ~loc (InvalidAppliedPatternName (c, info))
     end

  | Input.Patt_List ps ->
     let rec fold ~loc vars n = function
       | [] -> locate (Pattern.Patt_Constructor (Name.Predefined.nil, [])) loc, vars, n
       | p :: ps ->
          let p, vars, n = pattern ctx vars n p in
          let ps, vars, n = fold ~loc:(p.Location.loc) vars n ps in
          locate (Pattern.Patt_Constructor (Name.Predefined.cons, [p ; ps])) loc, vars, n
     in
     fold ~loc vars n ps

  | Input.Patt_Tuple ps ->
     let rec fold vars n ps = function
       | [] ->
          let ps = List.rev ps in
          locate (Pattern.Patt_Tuple ps) loc, vars, n
       | p::rem ->
          let p, vars, n = pattern ctx vars n p in
          fold vars n (p::ps) rem
     in
     fold vars n [] ps

let rec comp ~yield ctx {Location.thing=c';loc} =
  match c' with
  | Input.Handle (c, hcs) ->
     let c = comp ~yield ctx c
     and h = handler ~loc ctx hcs in
     locate (Dsyntax.With (h, c)) loc

  | Input.With (c1, c2) ->
     let c1 = comp ~yield ctx c1
     and c2 = comp ~yield ctx c2 in
     locate (Dsyntax.With (c1, c2)) loc

  | Input.Let (lst, c) ->
     let ctx, lst = let_clauses ~loc ~yield ctx lst in
     let c = comp ~yield ctx c in
     locate (Dsyntax.Let (lst, c)) loc

  | Input.LetRec (lst, c) ->
     let ctx, lst = letrec_clauses ~loc ~yield ctx lst in
     let c = comp ~yield ctx c in
     locate (Dsyntax.LetRec (lst, c)) loc

  | Input.MLAscribe (c, sch) ->
     let c = comp ~yield ctx c in
     let sch = ml_schema ctx sch in
     locate (Dsyntax.MLAscribe (c, sch)) loc

  | Input.Now (x,c1,c2) ->
     let x = comp ~yield ctx x
     and c1 = comp ~yield ctx c1
     and c2 = comp ~yield ctx c2 in
     locate (Dsyntax.Now (x,c1,c2)) loc

  | Input.Current c ->
     let c = comp ~yield ctx c in
     locate (Dsyntax.Current c) loc

  | Input.Lookup c ->
     let c = comp ~yield ctx c in
     locate (Dsyntax.Lookup c) loc

  | Input.Ref c ->
     let c = comp ~yield ctx c in
     locate (Dsyntax.Ref c) loc

  | Input.Update (c1, c2) ->
     let c1 = comp ~yield ctx c1
     and c2 = comp ~yield ctx c2 in
     locate (Dsyntax.Update (c1, c2)) loc

  | Input.Sequence (c1, c2) ->
     let c1 = comp ~yield ctx c1
     and c2 = comp ~yield ctx c2 in
     locate (Dsyntax.Sequence (c1, c2)) loc

  | Input.Assume ((x, t), c) ->
     let t = comp ~yield ctx t in
     let ctx = Ctx.add_variable x ctx in
     let c = comp ~yield ctx c in
     locate (Dsyntax.Assume ((x, t), c)) loc

  | Input.Where (c1, c2, c3) ->
     let c1 = comp ~yield ctx c1
     and c2 = comp ~yield ctx c2
     and c3 = comp ~yield ctx c3 in
     locate (Dsyntax.Where (c1, c2, c3)) loc

  | Input.Match (c, cases) ->
     let c = comp ~yield ctx c
     and cases = List.map (match_case ~yield ctx) cases in
     locate (Dsyntax.Match (c, cases)) loc

  | Input.Ascribe (c, t) ->
     let t = comp ~yield ctx t
     and c = comp ~yield ctx c in
     locate (Dsyntax.Ascribe (c, t)) loc

  | Input.External s ->
     locate (Dsyntax.External s) loc

  | Input.Lambda (xs, c) ->
     let rec fold ctx ys = function
       | [] ->
          let c = comp ~yield ctx c in
          mk_lambda ~loc ys c
       | (x, None) :: xs ->
          let ctx = Ctx.add_variable x ctx
          and ys = (x, None) :: ys in
          fold ctx ys xs
       | (x, Some t) :: xs ->
          let ys = (let t = comp ~yield ctx t in (x, Some t) :: ys)
          and ctx = Ctx.add_variable x ctx in
          fold ctx ys xs
     in
     fold ctx [] xs

  | Input.Spine (e, cs) ->
     spine ~yield ctx e cs

  | Input.Prod (xs, c) ->
     let rec fold ctx ys = function
       | [] ->
          let c = comp ~yield ctx c in
          mk_prod ~loc ys c
       | (x,t) :: xs ->
          let ys = (let t = comp ~yield ctx t in (x, t) :: ys) in
          let ctx = Ctx.add_variable x ctx in
          fold ctx ys xs
     in
     fold ctx [] xs

  | Input.Eq (c1, c2) ->
     let c1 = comp ~yield ctx c1
     and c2 = comp ~yield ctx c2 in
     locate (Dsyntax.Eq (c1, c2)) loc

  | Input.Refl c ->
     let c = comp ~yield ctx c in
     locate (Dsyntax.Refl c) loc

  | Input.Var x ->
     begin match Ctx.find ~loc x ctx with
     | Variable i -> locate (Dsyntax.Bound i) loc
     | Constant -> locate (Dsyntax.Constant x) loc
     | Constructor k ->
        if k = 0 then locate (Dsyntax.Constructor (x, [])) loc
        else error ~loc (ArityMismatch (x, 0, k))
     | Operation k ->
        if k = 0 then locate (Dsyntax.Operation (x, [])) loc
        else error ~loc (ArityMismatch (x, 0, k))
     end

  | Input.Type ->
     locate Dsyntax.Type loc

  | Input.Yield c ->
     if yield
     then
       let c = comp ~yield ctx c in
       locate (Dsyntax.Yield c) loc
     else
      error ~loc UnboundYield

  | Input.Function (xs, c) ->
     let rec fold ctx = function
       | [] -> comp ~yield ctx c
       | (x, t) :: xs ->
          let ctx = Ctx.add_variable x ctx in
          let c = fold ctx xs in
          let t = arg_annotation ctx t in
          locate (Dsyntax.Function (x, t, c)) loc
     in
     fold ctx xs

  | Input.Handler hcs ->
     handler ~loc ctx hcs

  | Input.List cs ->
     let rec fold ~loc = function
       | [] -> locate (Dsyntax.Constructor (Name.Predefined.nil, [])) loc
       | c :: cs ->
          let c = comp ~yield ctx c in
          let cs = fold ~loc:(c.Location.loc) cs in
          locate (Dsyntax.Constructor (Name.Predefined.cons, [c ; cs])) loc
     in
     fold ~loc cs

  | Input.Tuple cs ->
     let lst = List.map (comp ~yield ctx) cs in
     locate (Dsyntax.Tuple lst) loc

  | Input.CongrProd (e1, e2, e3) ->
     let e1 = comp ~yield ctx e1
     and e2 = comp ~yield ctx e2
     and e3 = comp ~yield ctx e3 in
     locate (Dsyntax.CongrProd (e1, e2, e3)) loc

  | Input.CongrApply (e1, e2, e3, e4, e5) ->
     let e1 = comp ~yield ctx e1
     and e2 = comp ~yield ctx e2
     and e3 = comp ~yield ctx e3
     and e4 = comp ~yield ctx e4
     and e5 = comp ~yield ctx e5 in
     locate (Dsyntax.CongrApply (e1, e2, e3, e4, e5)) loc

  | Input.CongrLambda (e1, e2, e3, e4) ->
     let e1 = comp ~yield ctx e1
     and e2 = comp ~yield ctx e2
     and e3 = comp ~yield ctx e3
     and e4 = comp ~yield ctx e4 in
     locate (Dsyntax.CongrLambda (e1, e2, e3, e4)) loc

  | Input.CongrEq (e1, e2, e3) ->
     let e1 = comp ~yield ctx e1
     and e2 = comp ~yield ctx e2
     and e3 = comp ~yield ctx e3 in
     locate (Dsyntax.CongrEq (e1, e2, e3)) loc

  | Input.CongrRefl (e1, e2) ->
     let e1 = comp ~yield ctx e1
     and e2 = comp ~yield ctx e2 in
     locate (Dsyntax.CongrRefl (e1, e2)) loc

  | Input.BetaStep (e1, e2, e3, e4, e5) ->
     let e1 = comp ~yield ctx e1
     and e2 = comp ~yield ctx e2
     and e3 = comp ~yield ctx e3
     and e4 = comp ~yield ctx e4
     and e5 = comp ~yield ctx e5 in
     locate (Dsyntax.BetaStep (e1, e2, e3, e4, e5)) loc

  | Input.String s ->
     locate (Dsyntax.String s) loc

  | Input.Context c ->
     let c = comp ~yield ctx c in
     locate (Dsyntax.Context c) loc

  | Input.Occurs (c1,c2) ->
     let c1 = comp ~yield ctx c1
     and c2 = comp ~yield ctx c2 in
     locate (Dsyntax.Occurs (c1,c2)) loc

  | Input.Natural c ->
     let c = comp ~yield ctx c in
     locate (Dsyntax.Natural c) loc

and let_clauses ~loc ~yield ctx lst =
  let rec fold ctx' lst' = function
    | [] ->
       let lst' = List.rev lst' in
       ctx', lst'
    | Input.Let_clause_ML (x, ys, sch, c) :: clauses ->
       let c = let_clause ~yield ctx ys c in
       let sch = let_annotation ctx sch in
       let ctx' = Ctx.add_variable x ctx' in
       let lst' = Dsyntax.Let_clause_ML (x, sch, c) :: lst' in
       fold ctx' lst' clauses
    | Input.Let_clause_tt (x, t, c) :: clauses ->
       let c = let_clause_tt ~yield ctx c t in
       let sch = Dsyntax.Let_annot_none in
       let ctx' = Ctx.add_variable x ctx' in
       let lst' = Dsyntax.Let_clause_ML (x, sch, c) :: lst' in
       fold ctx' lst' clauses
    | Input.Let_clause_patt (pt, c) :: clauses ->
     let c = comp ~yield ctx c in
     let ctx', xs, pt = bind_pattern ~yield ctx' pt in
     let lst' = Dsyntax.Let_clause_patt (xs, pt, c) :: lst' in
     fold ctx' lst' clauses
  in
  let rec check_unique forbidden = function
    | [] -> ()
    | Input.Let_clause_ML (x, _, _, _) :: lst
    | Input.Let_clause_tt (x, _, _) :: lst ->
       if List.mem x forbidden
       then error ~loc (ParallelShadowing x)
       else check_unique (x :: forbidden) lst
    | Input.Let_clause_patt (pt, _) :: lst ->
       let _, vars, _ = pattern ctx [] 0 pt in
       let xs = List.map fst vars in
       begin
         try
           let x = List.find (fun x -> List.mem x forbidden) xs in
           error ~loc (ParallelShadowing x)
         with Not_found ->
           check_unique (xs @ forbidden) lst
       end
  in
  check_unique [] lst ;
  fold ctx [] lst

and letrec_clauses ~loc ~yield ctx lst =
  let ctx =
    List.fold_left (fun ctx (f, _, _, _, _) -> Ctx.add_variable f ctx) ctx lst
  in
  let rec fold lst' = function
    | [] ->
       let lst' = List.rev lst' in
       ctx, lst'
    | (f, yt, ys, sch, c) :: xcs ->
       if List.exists (fun (g, _, _, _, _) -> Name.eq_ident f g) xcs
       then
         error ~loc (ParallelShadowing f)
       else
         let yt, c = letrec_clause ~yield ctx yt ys c in
         let sch = let_annotation ctx sch in
         let lst' = (f, yt, sch, c) :: lst' in
         fold lst' xcs
  in
  fold [] lst

and let_clause ~yield ctx ys c =
  let rec fold ctx = function
    | [] ->
       comp ~yield ctx c
    | (y, t) :: ys ->
       let ctx = Ctx.add_variable y ctx in
       let c = fold ctx ys in
       let t = arg_annotation ctx t in
       locate (Dsyntax.Function (y, t, c)) (c.Location.loc) (* XXX improve location *)
  in
  fold ctx ys

and let_clause_tt ~yield ctx c t =
  let c = comp ~yield ctx c
  and t = comp ~yield ctx t in
  locate (Dsyntax.Ascribe (c, t)) (c.Location.loc)

and letrec_clause ~yield ctx (y, t) ys c =
  let t = arg_annotation ctx t in
  let ctx = Ctx.add_variable y ctx in
  let c = let_clause ~yield ctx ys c in
  (y, t), c


and ml_schema ctx {Location.thing=Input.ML_Forall (params, t); loc} =
  locate (Dsyntax.ML_Forall (params, mlty ctx params t)) loc


and arg_annotation ctx = function
  | Input.Arg_annot_none -> Dsyntax.Arg_annot_none
  | Input.Arg_annot_ty t ->
     let t = mlty ctx [] t in
     Dsyntax.Arg_annot_ty t


and let_annotation ctx = function

  | Input.Let_annot_none ->
     Dsyntax.Let_annot_none

  | Input.Let_annot_schema sch ->
     let sch = ml_schema ctx sch in
     Dsyntax.Let_annot_schema sch

(* Desugar a spine. This function is a bit messy because we need to untangle
   to env. But it's worth doing to make users happy. TODO outdated comment *)
and spine ~yield ctx ({Location.thing=c';loc} as c) cs =

  (* Auxiliary function which splits a list into two parts with k
     elements in the first part. *)
  let split x k lst =
    let n = List.length lst in
    if n < k
    then
      error ~loc (ArityMismatch (x, n, k))
    else
    let rec split acc k lst =
      if k = 0 then
        List.rev acc, lst
      else
        match lst with
        | [] -> assert false
        | x :: lst -> split (x :: acc) (k - 1) lst
    in
    split [] k lst
  in

  (* First we calculate the head of the spine, and the remaining arguments. *)
  let c, cs =
    match c' with
    | Input.Var x ->
       begin match Ctx.find ~loc x ctx with
       | Variable i ->
          locate (Dsyntax.Bound i) loc, cs
       | Constant ->
          locate (Dsyntax.Constant x) loc, cs
       | Constructor k ->
          let cs', cs = split x k cs in
          data ~loc ~yield ctx x cs', cs
       | Operation k ->
          let cs', cs = split x k cs in
          operation ~loc ~yield ctx x cs', cs
       end

    | _ -> comp ~yield ctx c, cs
  in

  (* TODO improve locs *)
  List.fold_left (fun h arg ->
      let arg = comp ~yield ctx arg in
      locate (Dsyntax.Apply (h, arg)) (Location.union loc arg.Location.loc)) c cs

(* Desugar handler cases. *)
and handler ~loc ctx hcs =
  (* for every case | #op p => c we do #op binder => match binder with | p => c end *)
  let rec fold val_cases op_cases finally_cases = function
    | [] ->
       List.rev val_cases, Name.IdentMap.map List.rev op_cases, List.rev finally_cases

    | Input.CaseVal c :: hcs ->
       (* XXX if this handler is in a outer handler's operation case, should we use its yield?
          eg handle ... with | op => handler | val x => yield x end end *)
       let case = match_case ~yield:false ctx c in
       fold (case::val_cases) op_cases finally_cases hcs

    | Input.CaseOp (op, ((ps,_,_) as c)) :: hcs ->
       let k = Ctx.get_operation ~loc op ctx in
       let n = List.length ps in
       if n = k
       then
         let case = match_op_case ~yield:true ctx c in
         let my_cases = try Name.IdentMap.find op op_cases with | Not_found -> [] in
         let my_cases = case::my_cases in
         fold val_cases (Name.IdentMap.add op my_cases op_cases) finally_cases hcs
       else
         error ~loc (ArityMismatch (op, n, k))

    | Input.CaseFinally c :: hcs ->
       let case = match_case ~yield:false ctx c in
       fold val_cases op_cases (case::finally_cases) hcs

  in
  let handler_val, handler_ops, handler_finally = fold [] Name.IdentMap.empty [] hcs in
  locate (Dsyntax.Handler (Dsyntax.{ handler_val ; handler_ops ; handler_finally })) loc

(* Desugar a pattern and bind its variables *)
and bind_pattern ~yield ctx p =
  let p, vars, _ = pattern ctx [] 0 p in
  let rec fold xs ctx = function
    | [] -> xs, ctx
    | (x,_)::rem -> fold (x::xs) (Ctx.add_variable x ctx) rem
  in
  let xs, ctx = fold [] ctx vars in
  (ctx, xs, p)

(* Desugar a match case *)
and match_case ~yield ctx (p, c) =
  let ctx, xs, p = bind_pattern ~yield ctx p in
  let c = comp ~yield ctx c in
  (xs, p, c)

and match_op_case ~yield ctx (ps, pt, c) =
  let rec fold_patterns ps vars n = function
    | [] -> List.rev ps, vars, n
    | p::rem ->
       let p, vars, n = pattern ctx vars n p in
       fold_patterns (p::ps) vars n rem
  in
  let ps, vars, n = fold_patterns [] [] 0 ps in
  let pt, vars = match pt with
    | Some p ->
       let p, vars, n = pattern ctx vars n p in
       Some p, vars
    | None ->
       None, vars
  in
  let rec fold xs ctx = function
    | [] -> xs, ctx
    | (x,_)::rem -> fold (x::xs) (Ctx.add_variable x ctx) rem
  in
  let xs, ctx = fold [] ctx vars in
  let c = comp ~yield ctx c in
  (xs, ps, pt, c)

and data ~loc ~yield ctx x cs =
  let cs = List.map (comp ~yield ctx) cs in
  locate (Dsyntax.Constructor (x, cs)) loc

and operation ~loc ~yield ctx x cs =
  let cs = List.map (comp ~yield ctx) cs in
  locate (Dsyntax.Operation (x, cs)) loc


let decl_operation ~loc ctx args res =
  let args = List.map (mlty ctx []) args
  and res = mlty ctx [] res in
  args, res


let mlty_def ~loc ctx outctx params def =
  match def with
  | Input.ML_Alias ty ->
     let ty = mlty ctx params ty in
     outctx, Dsyntax.ML_Alias ty
  | Input.ML_Sum lst ->
    let rec fold outctx res = function
      | [] -> outctx, Dsyntax.ML_Sum (List.rev res)
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
     ctx, Dsyntax.ML_Alias ty
  | Input.ML_Sum lst ->
    let rec fold ctx res = function
      | [] -> ctx, Dsyntax.ML_Sum (List.rev res)
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
         error ~loc (ParallelShadowing t)
       else
         let ctx, def = mlty_rec_def ~loc ctx params def in
         fold ctx ((t, (params, def)) :: defs) lst
  in
  fold ctx [] lst

let rec toplevel ~basedir ctx {Location.thing=cmd; loc} =
  match cmd with

    | Input.DeclOperation (op, (args, res)) ->
       let args, res = decl_operation ~loc ctx args res in
       let ctx = Ctx.add_operation ~loc op (List.length args) ctx in
       (ctx, locate (Dsyntax.DeclOperation (op, (args, res))) loc)

    | Input.DefMLType lst ->
       let ctx, lst = mlty_defs ~loc ctx lst in
       (ctx, locate (Dsyntax.DefMLType lst) loc)

    | Input.DefMLTypeRec lst ->
       let ctx, lst = mlty_rec_defs ~loc ctx lst in
       (ctx, locate (Dsyntax.DefMLTypeRec lst) loc)

    | Input.DeclConstants (xs, u) ->
       let u = comp ~yield:false ctx u
       and ctx = List.fold_left (fun ctx x -> Ctx.add_constant ~loc x ctx) ctx xs in
       (ctx, locate (Dsyntax.DeclConstants (xs, u)) loc)

    | Input.TopHandle lst ->
       let lst =
         List.map
           (fun (op, (xs, y, c)) ->
              let k = Ctx.get_operation ~loc op ctx in
              let n = List.length xs in
              if n = k
              then
                let rec fold ctx xs' = function
                  | [] -> ctx, List.rev xs'
                  | None :: xs ->
                     let x = Name.anonymous () in
                     fold (Ctx.add_variable x ctx) (x::xs') xs
                  | Some x :: xs ->
                    if List.exists (function None -> false | Some y -> Name.eq_ident x y) xs
                    then error ~loc (ParallelShadowing x)
                    else fold (Ctx.add_variable x ctx) (x::xs') xs
                in
                let ctx, xs = fold ctx [] xs in
                let ctx = match y with | Some y -> Ctx.add_variable y ctx | None -> ctx in
                op, (xs, y, comp ~yield:false ctx c)
              else
                error ~loc (ArityMismatch (op, n, k))
           )
           lst
       in
       (ctx, locate (Dsyntax.TopHandle lst) loc)

    | Input.TopLet lst ->
       let ctx, lst = let_clauses ~loc ~yield:false ctx lst in
       (ctx, locate (Dsyntax.TopLet lst) loc)

    | Input.TopLetRec lst ->
       let ctx, lst = letrec_clauses ~loc ~yield:false ctx lst in
       (ctx, locate (Dsyntax.TopLetRec lst) loc)

    | Input.TopDynamic (x, annot, c) ->
       let c = comp ~yield:false ctx c in
       let ctx = Ctx.add_variable x ctx in
       let annot = arg_annotation ctx annot in
       (ctx, locate (Dsyntax.TopDynamic (x, annot, c)) loc)

    | Input.TopNow (x, c) ->
       let x = comp ~yield:false ctx x in
       let c = comp ~yield:false ctx c in
       (ctx, locate (Dsyntax.TopNow (x, c)) loc)

    | Input.TopDo c ->
       let c = comp ~yield:false ctx c in
       (ctx, locate (Dsyntax.TopDo c) loc)

    | Input.TopFail c ->
       let c = comp ~yield:false ctx c in
       (ctx, locate (Dsyntax.TopFail c) loc)

    | Input.Verbosity n ->
       (ctx, locate (Dsyntax.Verbosity n) loc)

    | Input.Require fs ->
      let rec fold ctx res = function
        | [] -> (ctx, locate (Dsyntax.Included (List.rev res)) loc)
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
    let cmds = Lexer.read_file ?line_limit:None Parser.file fn in
    let ctx, cmds = List.fold_left (fun (ctx,cmds) cmd ->
        let ctx, cmd = toplevel ~basedir ctx cmd in
        (ctx, cmd::cmds))
      (ctx,[]) cmds
    in
    ctx, List.rev cmds
