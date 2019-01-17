(** Conversion from sugared to desugared input syntax.
    The responsibilities of this phase are:

    - Convert all references to entities to de Bruijn indices, levels,
      and paths (i.e., sequences of levels).

    - Check that the following entities are applied with the correct arity:
      operations, type constructors, TT constructors, ML constructors.
      (This may be delegate to typechecking in the future, it's here for
       historic reasons.)
*)

(** The arity of an operation or a data constructor. *)
type arity = Arity of int

(** De bruijn level *)
type level = Level of int

(** de Bruijn index *)
type index = Index of int

(** Information about names *)
type info =
  | Variable
  | TTConstructor of arity
  | MLConstructor of arity
  | Operation of arity

let print_info info ppf = match info with
  | Variable -> Format.fprintf ppf "a value"
  | TTConstructor _ -> Format.fprintf ppf "a constructor"
  | MLConstructor _ -> Format.fprintf ppf "an ML constructor"
  | Operation _ -> Format.fprintf ppf "an operation"

type error =
  | UnknownPath of Name.path
  | UnknownType of Name.path
  | NameAlreadyDeclared of Name.t * info
  | MLTypeAlreadyDeclared of Name.t
  | OperationExpected : Name.path * info -> error
  | InvalidTermPatternName : Name.t * info -> error
  | InvalidPatternName : Name.t * info -> error
  | InvalidAppliedPatternName : Name.t * info -> error
  | NonlinearPattern : Name.t -> error
  | ArityMismatch of Name.path * int * arity
  | UnboundYield
  | ParallelShadowing of Name.t
  | AppliedTyParam
  | RequiredModuleMissing of Name.t * string list
  | CircularRequire of Name.t list

let print_error err ppf = match err with

  | UnknownPath pth ->
     Format.fprintf ppf "unknown name %t"
       (Name.print_path pth)

  | UnknownType pth ->
     Format.fprintf ppf "unknown type %t"
       (Name.print_path pth)

  | NameAlreadyDeclared (x, info) ->
     Format.fprintf ppf
       "%t is already declared as a %t"
       (Name.print x)
       (print_info info)

  | MLTypeAlreadyDeclared x ->
     Format.fprintf ppf
       "%t is already a defind ML type"
       (Name.print x)

  | OperationExpected (pth, info) ->
     Format.fprintf ppf "%t should be an operation but is %t"
       (Name.print_path pth)
       (print_info info)

  | InvalidTermPatternName (x, info) ->
     Format.fprintf ppf "%t cannot be used in a term pattern as it is %t"
       (Name.print x)
       (print_info info)

  | InvalidPatternName (x, info) ->
     Format.fprintf ppf "%t cannot be used in a pattern as it is %t"
       (Name.print x)
       (print_info info)

  | InvalidAppliedPatternName (x, info) ->
     Format.fprintf ppf "%t cannot be applied in a pattern as it is %t"
       (Name.print x)
       (print_info info)

  | NonlinearPattern x ->
     Format.fprintf ppf "non-linear pattern variable %t is not allowed."
       (Name.print x)

  | ArityMismatch (pth, used, Arity expected) ->
     Format.fprintf ppf "%t expects %d arguments but is used with %d"
       (Name.print_path pth)
       expected
       used

  | UnboundYield ->
     Format.fprintf ppf "yield may only appear in a handler"

  | ParallelShadowing x ->
     Format.fprintf ppf "%t is bound more than once"
       (Name.print x)

  | AppliedTyParam ->
     Format.fprintf ppf "an ML type parameter cannot be applied"

  | RequiredModuleMissing (mdl_name, files) ->
     Format.fprintf ppf "required module %t could not be found, looked in:@\n@[<hv>%t@]"
       (Name.print mdl_name)
       (Print.sequence (fun fn ppf -> Format.fprintf ppf "%s" fn) "," files)

  | CircularRequire mdls ->
     Format.fprintf ppf "circuar module dependency (@[<hov -2>%t@])"
        (Print.sequence Name.print "," mdls)

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

module Ctx = struct

  (* A module has two name spaces, one for ML types and the other for everything
     else. *)
  type ml_module = {
      ml_types : (Name.t * arity) list ;
      ml_names : (Name.t * info) list
    }

  let empty_module = { ml_types = []; ml_names = [] }

  type t = {
      (* Known ML modules *)
      ml_modules : (Name.t * ml_module) list;
      (* Current module *)
      current : ml_module ;
      (* Chain of modules being loaded (for dependency cycle detection) *)
      loading : Name.t list;
    }

  let empty = {
      ml_modules = [];
      current = empty_module;
      loading = []
    }

  (* Lookup functions named [find_XYZ] return optional results,
     while those named [get_XYZ] require a location and either return
     a result or trigger an error. *)

  (* Find in the association list and return with de Bruijn index. *)
  let find_index x lst =
    let rec search i = function
      | [] -> None
      | (y, d) :: ys ->
         if Name.equal x y then Some (d, Index i) else search (i+1) ys
    in
    search 0 lst

  (* Find in the association list and return with de Bruijn level. *)
  let find_level x lst =
    let rec search = function
      | [] -> None
      | (y, d) :: ys ->
         if Name.equal x y then Some (d, Level (List.length ys)) else search ys
    in
    search lst

  (* Find the level of the module and its contents *)
  let find_module mdl_name mdls =
    find_level mdl_name mdls

  (* Find the information about the given path *)
  let find_info_path pth ctx =
    match pth with

    | Name.PName x ->
       begin
         match find_index x ctx.current.ml_names with
         | None -> None
         | Some (info, Index x_ind) -> Some (info, Dsyntax.PName (Dsyntax.Index (x, x_ind)))
       end

    | Name.PModule (mdl_name, x) ->
       begin match find_module mdl_name ctx.ml_modules with
         | None -> None
         | Some (mdl, Level mdl_lvl) ->
            begin
              match find_level x mdl.ml_names with
              | None -> None
              | Some (info, Level x_lvl) ->
                 Some (info,
                       Dsyntax.PModule (Dsyntax.Level (mdl_name, mdl_lvl), Dsyntax.Level (x, x_lvl)))
            end
       end

  (* Find the path and arity of the given ML type *)
  let find_ml_type_path pth ctx =
    match pth with

    | Name.PName t ->
       begin
         match find_level t ctx.current.ml_types with
         | None -> None
         | Some (info, Level t_lvl) ->
       end

    | Name.PModule (mdl_name, t) ->
       begin match find_module mdl_name ctx.ml_modules with
         | None -> None
         | Some (mdl, _) -> find_ml_type_name t mdl.ml_types
       end

  (* Check that the name is not bound already *)
  let check_is_fresh_name ~loc x ctx =
    match find_info_name x ctx.current.ml_names with
    | None -> ()
    | Some info -> error ~loc (NameAlreadyDeclared (x, info))

  (* Check that the type is not bound already *)
  let check_is_fresh_type ~loc x ctx =
    match find_info_name x ctx.current.ml_types with
    | None -> ()
    | Some _ -> error ~loc (MLTypeAlreadyDeclared x)

  (* Get the info about a path, or fail *)
  let get_info_path ~loc pth ctx =
    match find_info_path pth ctx with
    | None -> error ~loc (UnknownPath pth)
    | Some info -> info

  (* Get the arity of an operation, or fail *)
  let get_operation ~loc pth ctx =
    match get_info_path ~loc pth ctx with
    | Operation k -> k
    | (Variable | TTConstructor _ | MLConstructor _) as info ->
      error ~loc (OperationExpected (pth, info))

  (* Get the arity and de Bruijn level of type named [t] and its definition *)
  let get_ml_type ~loc pth ctx =
    match find_ml_type_path pth ctx with
    | None -> error ~loc (UnknownType pth)
    | Some a -> a

  (* Add a module to the module list, allow shadowing. *)
  let add_module mdl_name mdl ctx =
    { ctx with ml_modules = (mdl_name, mdl) :: ctx.ml_modules }

  (* Add infomation about a name *)
  let add_info ~loc ~shadow x info ctx =
    if not shadow then check_is_fresh_name ~loc x ctx ;
    { ctx with current = { ctx.current with ml_names = (x, info) :: ctx.current.ml_names } }

  (* Add a local named value, may shadow existing names *)
  let add_value ~loc x ctx =
    add_info ~loc ~shadow:true x Variable ctx

  (* Add a toplevel named value, may not shadow existing names *)
  let add_top_value ~loc x ctx =
    add_info ~loc ~shadow:false x Variable ctx

  (* Add an ML constructor of given arity *)
  let add_ml_constructor ~loc c arity ctx =
    add_info ~loc ~shadow:false c (MLConstructor (Arity arity)) ctx

  (* Add a TT constructor of given arity *)
  let add_tt_constructor ~loc c arity ctx =
    add_info ~loc ~shadow:false c (TTConstructor (Arity arity)) ctx

  (* Add to the context the fact that [t] is a type constructor with [k] parameters. *)
  let add_ml_type ~loc t k ctx  =
    check_is_fresh_type ~loc t ctx ;
    { ctx with current = { ctx.current with  ml_types = (t, Arity k) :: ctx.current.ml_types } }

  (* Has the given file already been loaded? *)
  let loaded mdl {ml_modules; _} =
    List.exists (fun (m, _) -> (mdl = m)) ml_modules

  (* Push a module onto the loading stack. *)
  let push_module mdl_name ctx = { ctx with loading = mdl_name :: ctx.loading }

  (* Pop a module off the loading stack. *)
  let pop_module ctx =
    { ctx with loading =
                 match ctx.loading with
                 | [] -> []
                 | _ :: mdls -> mdls
    }

  (* Is the given file being loaded at the moment? *)
  let loading mdl_name {loading; _} =
    List.mem mdl_name loading

end (* module Ctx *)

let locate = Location.locate

let mlty_judgement = function
  | Input.ML_IsType -> Dsyntax.ML_IsType
  | Input.ML_IsTerm -> Dsyntax.ML_IsTerm
  | Input.ML_EqType -> Dsyntax.ML_EqType
  | Input.ML_EqTerm -> Dsyntax.ML_EqTerm

let rec mlty_abstracted_judgement = function

  | Input.ML_NotAbstract frm ->
     let frm = mlty_judgement frm in
     Dsyntax.ML_NotAbstract frm

  | Input.ML_Abstract abstr ->
     let abstr = mlty_abstracted_judgement abstr in
     Dsyntax.ML_Abstract abstr

(* Desugar an ML type, with the given list of known type parameters *)
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

      | Input.ML_TyApply (pth, args) ->
         begin match pth with

         | Name.PName x ->

            let rec search k = function
              | [] ->
              (* It's a type name *)
              begin
                let (l, arity) = Ctx.get_ml_type_name ~loc x ctx in
                let n = List.length args in
                if arity = n
                then
                  let args = List.map mlty args in
                  Dsyntax.ML_TyApply (Dsyntax.TName (Dsyntax.Level (x, l)), args)
                else
                  error ~loc (ArityMismatch (pth, n, arity))
              end
              | None :: lst -> search k lst
              | Some y :: lst ->
                 if Name.equal x y then
                   (* It's a type parameter *)
                   begin match args with
                   | [] -> Dsyntax.ML_Bound k
                   | _::_ -> error ~loc AppliedTyParam
                   end
                 else search (k+1)
            in
            search 0 params

         | Name.PModule _ ->
            begin
            end
         end

      | Input.ML_Anonymous ->
         Dsyntax.ML_Anonymous

      | Input.ML_Judgement abstr ->
         let abstr = mlty_abstracted_judgement abstr
         in Dsyntax.ML_Judgement abstr

      | Input.ML_String -> Dsyntax.ML_String
      end
    in
    locate ty' loc
  in
  mlty ty

(* TODO improve locs *)
let mk_abstract ~loc ys c =
  List.fold_left
    (fun c (y,u) -> locate (Dsyntax.Abstract (y,u,c)) loc)
    c ys

let rec tt_pattern ctx {Location.thing=p';loc} =
  match p' with
  | Input.Patt_TT_Anonymous ->
     ctx, locate Dsyntax.Patt_TT_Anonymous loc

  | Input.Patt_TT_Var x ->
     (* NB: a pattern variable always shadows whatever it can *)
     let ctx = Ctx.add_variable x ctx in
     ctx, (locate (Dsyntax.Patt_TT_Var x) loc)

  | Input.Patt_TT_As (p1, p2) ->
     let ctx, p1 = tt_pattern ctx p1 in
     let ctx, p2 = tt_pattern ctx p2 in
     ctx, locate (Dsyntax.Patt_TT_As (p1, p2)) loc

  | Input.Patt_TT_Constructor (c, ps) ->
     begin match Ctx.find_ident ~loc c ctx with
     | TTConstructor k -> pattern_tt_constructor ~loc ctx c k ps
     | (MLConstructor _ | Operation _ | Variable _) as info ->
        error ~loc (InvalidTermPatternName (c, info))
     end

  | Input.Patt_TT_GenAtom p ->
     let ctx, p = tt_pattern ctx p in
     ctx, locate (Dsyntax.Patt_TT_GenAtom p) loc

  | Input.Patt_TT_IsType p ->
     let ctx, p = tt_pattern ctx p in
     ctx, locate (Dsyntax.Patt_TT_IsType p) loc

  | Input.Patt_TT_IsTerm (p1, p2) ->
     let ctx, p1 = tt_pattern ctx p1 in
     let ctx, p2 = tt_pattern ctx p2 in
     ctx, locate (Dsyntax.Patt_TT_IsTerm (p1, p2)) loc

  | Input.Patt_TT_EqType (p1, p2) ->
     let ctx, p1 = tt_pattern ctx p1 in
     let ctx, p2 = tt_pattern ctx p2 in
     ctx, locate (Dsyntax.Patt_TT_EqType (p1, p2)) loc

  | Input.Patt_TT_EqTerm (p1, p2, p3) ->
     let ctx, p1 = tt_pattern ctx p1 in
     let ctx, p2 = tt_pattern ctx p2 in
     let ctx, p3 = tt_pattern ctx p3 in
     ctx, locate (Dsyntax.Patt_TT_EqTerm (p1, p2, p3)) loc

  | Input.Patt_TT_Abstraction (abstr, p0) ->
     let rec fold ctx = function
       | [] -> tt_pattern ctx p0
       | (xopt, popt) :: abstr ->
          let ctx, popt =
            match popt with
            | None -> ctx, locate Dsyntax.Patt_TT_Anonymous loc
            | Some p ->
               let ctx, p = tt_pattern ctx p in
               ctx, p
          in
          let ctx, xopt =
            begin
              match xopt with
              | Some x ->
                 let ctx = Ctx.add_variable x ctx in
                 ctx, Some x
              | None -> ctx, None
            end
          in
          let ctx, p = fold ctx abstr in
          ctx, locate (Dsyntax.Patt_TT_Abstraction (xopt, popt,p)) loc
     in
     fold ctx abstr

and pattern_tt_constructor ~loc ctx c k ps =
  let k' = List.length ps in
  if k <> k' then
    error ~loc (ArityMismatch (c, k, k'))
  else
    let rec fold ctx ps = function
       | [] ->
          let ps = List.rev ps in
          ctx, locate (Dsyntax.Patt_TT_Constructor (c, ps)) loc
       | q :: qs ->
          let ctx, p = tt_pattern ctx q in
          fold ctx (p :: ps) qs
     in
     fold ctx [] ps

let rec pattern ctx {Location.thing=p; loc} =
  match p with
  | Input.Patt_Anonymous ->
     ctx, locate Dsyntax.Patt_Anonymous loc

  | Input.Patt_Var x ->
     begin match Ctx.find_opt_ident x ctx with

     | Some (Variable _)
        (* We allow shadowing. *)
     | None ->
        let ctx = Ctx.add_variable x ctx in
        ctx, locate (Dsyntax.Patt_Var x) loc

     | Some (MLConstructor k) ->
        if k = 0
        then ctx, locate (Dsyntax.Patt_Constr (x,[])) loc
        else error ~loc (ArityMismatch (x, 0, k))

     | Some ((TTConstructor _ | Operation _) as info) ->
        error ~loc (InvalidPatternName (x, info))

     end

  | Input.Patt_As (p1, p2) ->
     let ctx, p1 = pattern ctx p1 in
     let ctx, p2 = pattern ctx p2 in
     ctx, locate (Dsyntax.Patt_As (p1, p2)) loc

  | Input.Patt_Judgement p ->
     let ctx, p = tt_pattern ctx p in
     ctx, locate (Dsyntax.Patt_Judgement p) loc

  | Input.Patt_Constr (c,ps) ->
     begin match Ctx.find_ident ~loc c ctx with
     | MLConstructor k ->
        let len = List.length ps in
        if k = len
        then
          let rec fold ctx ps = function
            | [] ->
               let ps = List.rev ps in
               ctx, locate (Dsyntax.Patt_Constr (c, ps)) loc
            | p::rem ->
               let ctx, p = pattern ctx p in
               fold ctx (p::ps) rem
          in
          fold ctx [] ps
        else
          error ~loc (ArityMismatch (c, List.length ps, k))
     | (Variable _ | TTConstructor _ | Operation _) as info ->
        error ~loc (InvalidAppliedPatternName (c, info))
     end

  | Input.Patt_List ps ->
     let rec fold ~loc ctx = function
       | [] -> ctx, locate (Dsyntax.Patt_Constr (Name.Predefined.nil, [])) loc
       | p :: ps ->
          let ctx, p = pattern ctx  p in
          let ctx, ps = fold ~loc:(p.Location.loc) ctx ps in
          ctx, locate (Dsyntax.Patt_Constr (Name.Predefined.cons, [p ; ps])) loc
     in
     fold ~loc ctx ps

  | Input.Patt_Tuple ps ->
     let rec fold ctx ps = function
       | [] ->
          let ps = List.rev ps in
          ctx, locate (Dsyntax.Patt_Tuple ps) loc
       | p::rem ->
          let ctx, p = pattern ctx p in
          fold ctx (p::ps) rem
     in
     fold ctx [] ps



(** Verify that a pattern is linear and that it does not bind anything
    in the given set of forbidden names. Return the set of forbidden names
    extended with the names that this pattern binds. *)

let check_linear_pattern_variable ~loc ~forbidden x =
     if Name.IdentSet.mem x forbidden then
       error ~loc (NonlinearPattern x)
     else
       Name.IdentSet.add x forbidden

let rec check_linear_tt ?(forbidden=Name.IdentSet.empty) {Location.thing=p';loc} =
  match p' with

  | Input.Patt_TT_Anonymous -> forbidden

  | Input.Patt_TT_Var x ->
     check_linear_pattern_variable ~loc ~forbidden x

  | Input.Patt_TT_As (p1, p2)
  | Input.Patt_TT_IsTerm (p1, p2)
  | Input.Patt_TT_EqType (p1, p2) ->
     let forbidden = check_linear_tt ~forbidden p1 in
     check_linear_tt ~forbidden p2

  | Input.Patt_TT_Constructor (_, ps) ->
     List.fold_left (fun forbidden -> check_linear_tt ~forbidden) forbidden ps

  | Input.Patt_TT_GenAtom p ->
     check_linear_tt ~forbidden p

  | Input.Patt_TT_IsType p ->
     check_linear_tt ~forbidden p

  | Input.Patt_TT_EqTerm (p1, p2, p3) ->
     let forbidden = check_linear_tt ~forbidden p1 in
     let forbidden = check_linear_tt ~forbidden p2 in
     check_linear_tt ~forbidden p3

  | Input.Patt_TT_Abstraction (args, p) ->
     let forbidden = check_linear_abstraction ~loc ~forbidden args in
     check_linear_tt ~forbidden p

and check_linear_abstraction ~loc ~forbidden = function
  | [] -> forbidden
  | (xopt, popt) :: args ->
     let forbidden =
       match xopt with
       | None -> forbidden
       | Some x -> check_linear_pattern_variable ~loc ~forbidden x
     in
     let forbidden =
       match popt with
       | None -> forbidden
       | Some p -> check_linear_tt ~forbidden p
     in
     check_linear_abstraction ~loc ~forbidden args


let rec check_linear ?(forbidden=Name.IdentSet.empty) {Location.thing=p';loc} =
  match p' with

  | Input.Patt_Anonymous -> forbidden

  | Input.Patt_Var x ->
     check_linear_pattern_variable ~loc ~forbidden x

  | Input.Patt_As (p1, p2) ->
     let forbidden = check_linear ~forbidden p1 in
     check_linear ~forbidden p2

  | Input.Patt_Judgement pt ->
     check_linear_tt ~forbidden pt

  | Input.Patt_Constr (_, ps)
  | Input.Patt_List ps
  | Input.Patt_Tuple ps ->
     check_linear_list ~forbidden ps

and check_linear_list ~forbidden = function
  | [] -> forbidden
  | p :: ps ->
     let forbidden = check_linear ~forbidden p in
     check_linear_list ~forbidden ps

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
     let ctx = Ctx.add_opt_variable x ctx in
     let c = comp ~yield ctx c in
     locate (Dsyntax.Assume ((x, t), c)) loc

  | Input.Match (c, cases) ->
     let c = comp ~yield ctx c
     and cases = List.map (match_case ~yield ctx) cases in
     locate (Dsyntax.Match (c, cases)) loc

  | Input.Ascribe (c, t) ->
     let t = comp ~yield ctx t
     and c = comp ~yield ctx c in
     locate (Dsyntax.Ascribe (c, t)) loc


  | Input.Abstract (xs, c) ->
     let rec fold ctx ys = function
       | [] ->
          let c = comp ~yield ctx c in
          mk_abstract ~loc ys c
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

  | Input.Substitute (e, cs) ->
     let e = comp ~yield ctx e in
     List.fold_left
       (fun e c ->
          let c = comp ~yield ctx c
          and loc = Location.from_to loc c.Location.loc in

          locate (Dsyntax.Substitute (e, c)) loc)
       e cs

  | Input.Spine (e, cs) ->
     spine ~yield ctx e cs

  | Input.Var x ->
     begin match Ctx.find_ident ~loc x ctx with
     | Variable i -> locate (Dsyntax.Bound i) loc
     | TTConstructor k ->
        if k = 0 then locate (Dsyntax.TT_Constructor (x, [])) loc
        else error ~loc (ArityMismatch (x, 0, k))
     | MLConstructor k ->
        if k = 0 then locate (Dsyntax.MLConstructor (x, [])) loc
        else error ~loc (ArityMismatch (x, 0, k))
     | Operation k ->
        if k = 0 then locate (Dsyntax.Operation (x, [])) loc
        else error ~loc (ArityMismatch (x, 0, k))
     end

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
       | [] -> locate (Dsyntax.MLConstructor (Name.Predefined.nil, [])) loc
       | c :: cs ->
          let c = comp ~yield ctx c in
          let cs = fold ~loc:(c.Location.loc) cs in
          locate (Dsyntax.MLConstructor (Name.Predefined.cons, [c ; cs])) loc
     in
     fold ~loc cs

  | Input.Tuple cs ->
     let lst = List.map (comp ~yield ctx) cs in
     locate (Dsyntax.Tuple lst) loc

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

  | Input.Open (mdl, c) ->
     failwith "modules not implemented"

and let_clauses ~loc ~yield ctx lst =
  let rec fold ctx' lst' = function
    | [] ->
       let lst' = List.rev lst' in
       ctx', lst'

    | Input.Let_clause_ML (xys_opt, sch, c) :: clauses ->
       let ys = (match xys_opt with None -> [] | Some (_, ys) -> ys) in
       let c = let_clause ~yield ctx ys c in
       let sch = let_annotation ctx sch in
       let x, ctx' =
         begin match xys_opt with
         | None -> locate Dsyntax.Patt_Anonymous loc, ctx'
         (* XXX if x carried its location, we would use it here *)
         | Some (x, _) -> locate (Dsyntax.Patt_Var x) loc, Ctx.add_variable x ctx'
         end
       in
       let lst' = Dsyntax.Let_clause (x, sch, c) :: lst' in
       fold ctx' lst' clauses

    | Input.Let_clause_tt (xopt, t, c) :: clauses ->
       let c = let_clause_tt ~yield ctx c t in
       let sch = Dsyntax.Let_annot_none in
       let x, ctx' =
         begin match xopt with
         | None -> locate Dsyntax.Patt_Anonymous loc, ctx'
         (* XXX if x carried its location, we would use it here *)
         | Some x -> locate (Dsyntax.Patt_Var x) loc, Ctx.add_variable x ctx'
         end
       in
       let lst' = Dsyntax.Let_clause (x, sch, c) :: lst' in
       fold ctx' lst' clauses

    | Input.Let_clause_patt (pt, sch, c) :: clauses ->
       let c = comp ~yield ctx c in
       let sch = let_annotation ctx sch in
       let ctx', pt = pattern ctx' pt in
       let lst' = Dsyntax.Let_clause (pt, sch, c) :: lst' in

     fold ctx' lst' clauses
  in
  let rec check_unique forbidden = function
    | [] -> ()
    | Input.Let_clause_ML (Some (x, _), _, _) :: lst
    | Input.Let_clause_tt (Some x, _, _) :: lst ->
       if Name.IdentSet.mem x forbidden
       then error ~loc (ParallelShadowing x)
       else check_unique (Name.IdentSet.add x forbidden) lst
    | Input.Let_clause_ML (None, _, _) :: lst
    | Input.Let_clause_tt (None, _, _) :: lst ->
       check_unique forbidden lst
    | Input.Let_clause_patt (pt, _, _) :: lst ->
       let forbidden = check_linear ~forbidden pt in
       check_unique forbidden lst
  in
  check_unique Name.IdentSet.empty lst ;
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
         let lst' = Dsyntax.Letrec_clause (f, yt, sch, c) :: lst' in
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

(* To desugar a spine [c1 c2 ... cN], we check if c1 is an identifier, in which
   case we break the spine according to the arity of c1. *)
and spine ~yield ctx ({Location.thing=c';loc} as c) cs =

  (* Auxiliary function which splits a list into two parts with k
     elements in the first part. *)
  let split_at constr k lst =
    let rec split acc m lst =
      if m = 0 then
        List.rev acc, lst
      else
        match lst with
        | [] -> error ~loc (ArityMismatch (constr, List.length acc, k))
        | x :: lst -> split (x :: acc) (m - 1) lst
    in
    split [] k lst
  in

  (* First we calculate the head of the spine, and the remaining arguments. *)
  let head, cs =
    match c' with
    | Input.Var x ->
       begin match Ctx.find_ident ~loc x ctx with
       | Variable i ->
          locate (Dsyntax.Bound i) loc, cs
       | TTConstructor k ->
          let cs', cs = split_at x k cs in
          tt_constructor ~loc ~yield ctx x cs', cs
       | MLConstructor k ->
          let cs', cs = split_at x k cs in
          ml_constructor ~loc ~yield ctx x cs', cs
       | Operation k ->
          let cs', cs = split_at x k cs in
          operation ~loc ~yield ctx x cs', cs
       end

    | _ -> comp ~yield ctx c, cs
  in

  (* TODO improve locs *)
  List.fold_left
    (fun head arg ->
       let arg = comp ~yield ctx arg
       and loc = Location.union loc arg.Location.loc in
       let head = Dsyntax.Apply (head, arg) in
       locate head loc)
    head
    cs

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

(* Desugar a match case *)
and match_case ~yield ctx (p, g, c) =
  ignore (check_linear p) ;
  let ctx, p = pattern ctx p in
  let g = when_guard ~yield ctx g
  and c = comp ~yield ctx c in
  (p, g, c)

and when_guard ~yield ctx = function
  | None -> None
  | Some c ->
     let c = comp ~yield ctx c in
     Some c

and match_op_case ~yield ctx (ps, pt, c) =
  let rec fold ctx qs = function
    | [] ->
       let qs = List.rev qs in
       let ctx, pt =
         begin match pt with
         | None -> ctx, None
         | Some p ->
            ignore (check_linear_tt p) ;
            let ctx, p = tt_pattern ctx p in
            ctx, Some p
         end
       in
       let c = comp ~yield ctx c in
       (qs, pt, c)

    | p :: ps ->
       let ctx, q = pattern ctx p in
       fold ctx (q :: qs) ps
  in
  fold ctx [] ps

and ml_constructor ~loc ~yield ctx x cs =
  let cs = List.map (comp ~yield ctx) cs in
  locate (Dsyntax.MLConstructor (x, cs)) loc

and tt_constructor ~loc ~yield ctx x cs =
  let cs = List.map (comp ~yield ctx) cs in
  locate (Dsyntax.TT_Constructor (x, cs)) loc

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
        let outctx = Ctx.add_ml_constructor ~loc c (List.length args) outctx in
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
        let ctx = Ctx.add_ml_constructor ~loc c (List.length args) ctx in
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

let local_context ctx xcs m =
  let rec fold ctx xcs_out = function
    | [] ->
       let xcs_out = List.rev xcs_out in
       let v = m ctx in
       v, xcs_out
    | (x, c) :: xcs ->
       let c = comp ~yield:false ctx c in
       let ctx = Ctx.add_variable x ctx in
       fold ctx ((x,c) :: xcs_out) xcs
  in
  fold ctx [] xcs

let premise ctx {Location.thing=prem;loc} =
  match prem with
  | Input.PremiseIsType (mvar, local_ctx) ->
     let (), local_ctx = local_context ctx local_ctx (fun _ -> ()) in
     let ctx = Ctx.add_opt_variable mvar ctx in
     ctx, locate (Dsyntax.PremiseIsType (mvar, local_ctx)) loc

  | Input.PremiseIsTerm (mvar, local_ctx, c) ->
     let c, local_ctx =
       local_context
         ctx local_ctx
         (fun ctx -> comp ~yield:false ctx c)
     in
     let ctx = Ctx.add_opt_variable mvar ctx in
     ctx, locate (Dsyntax.PremiseIsTerm (mvar, local_ctx, c)) loc

  | Input.PremiseEqType (mvar, local_ctx, (c1, c2)) ->
     let c12, local_ctx =
       local_context
         ctx local_ctx
         (fun ctx ->
           comp ~yield:false ctx c1,
           comp ~yield:false ctx c2)
     in
     let ctx =
       match mvar with
       | None -> ctx
       | Some x -> Ctx.add_variable x ctx
     in
     ctx, locate (Dsyntax.PremiseEqType (mvar, local_ctx, c12)) loc

  | Input.PremiseEqTerm (mvar, local_ctx, (c1, c2, c3)) ->
     let c123, local_ctx =
       local_context ctx local_ctx
       (fun ctx ->
         comp ~yield:false ctx c1,
         comp ~yield:false ctx c2,
         comp ~yield:false ctx c3)
     in
     let ctx =
       match mvar with
       | None -> ctx
       | Some x -> Ctx.add_variable x ctx
     in
     ctx, locate (Dsyntax.PremiseEqTerm (mvar, local_ctx, c123)) loc

let premises ctx prems m =
  let rec fold ctx prems_out = function
    | [] ->
       let v = m ctx in
       let prems_out = List.rev prems_out in
       v, prems_out

    | prem :: prems ->
       let ctx, prem = premise ctx prem in
       fold ctx (prem :: prems_out) prems
  in
  fold ctx [] prems

let rec toplevel ~basedir ctx {Location.thing=cmd; loc} =
  match cmd with

  | Input.RuleIsType (rname, prems) ->
     let (), prems = premises ctx prems (fun _ -> ()) in
     let ctx = Ctx.add_tt_constructor ~loc rname (List.length prems) ctx in
     (ctx, locate (Dsyntax.RuleIsType (rname, prems)) loc)

  | Input.RuleIsTerm (rname, prems, c) ->
     let c, prems =
       premises
         ctx prems
         (fun ctx -> comp ~yield:false ctx c)
     in
     let ctx = Ctx.add_tt_constructor ~loc rname (List.length prems) ctx in
     (ctx, locate (Dsyntax.RuleIsTerm (rname, prems, c)) loc)

  | Input.RuleEqType (rname, prems, (c1, c2)) ->
     let c12, prems =
       premises
         ctx prems
         (fun ctx ->
           comp ~yield:false ctx c1,
           comp ~yield:false ctx c2)
     in
     let ctx = Ctx.add_tt_constructor ~loc rname (List.length prems) ctx in
     (ctx, locate (Dsyntax.RuleEqType (rname, prems, c12)) loc)

  | Input.RuleEqTerm (rname, prems, (c1, c2, c3)) ->
     let c123, prems =
       premises
         ctx prems
         (fun ctx ->
          comp ~yield:false ctx c1,
          comp ~yield:false ctx c2,
          comp ~yield:false ctx c3)
     in
     let ctx = Ctx.add_tt_constructor ~loc rname (List.length prems) ctx in
     (ctx, locate (Dsyntax.RuleEqTerm (rname, prems, c123)) loc)

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

  | Input.DeclExternal (x, sch, s) ->
     let sch = ml_schema ctx sch in
     let ctx = Ctx.add_variable x ctx in
     (ctx, locate (Dsyntax.DeclExternal (x, sch, s)) loc)

  | Input.TopLet lst ->
     let ctx, lst = let_clauses ~loc ~yield:false ctx lst in
     (ctx, locate (Dsyntax.TopLet lst) loc)

  | Input.TopLetRec lst ->
     let ctx, lst = letrec_clauses ~loc ~yield:false ctx lst in
     (ctx, locate (Dsyntax.TopLetRec lst) loc)

  | Input.TopComputation c ->
     let c = comp ~yield:false ctx c in
     (ctx, locate (Dsyntax.TopComputation c) loc)

  | Input.TopDynamic (x, annot, c) ->
     let c = comp ~yield:false ctx c in
     let ctx = Ctx.add_variable x ctx in
     let annot = arg_annotation ctx annot in
     (ctx, locate (Dsyntax.TopDynamic (x, annot, c)) loc)

  | Input.TopNow (x, c) ->
     let x = comp ~yield:false ctx x in
     let c = comp ~yield:false ctx c in
     (ctx, locate (Dsyntax.TopNow (x, c)) loc)

  | Input.Verbosity n ->
     (ctx, locate (Dsyntax.Verbosity n) loc)

  | Input.Require mdls ->
     ml_modules ~loc ~basedir ctx mdls

and ml_modules ~loc ~basedir ctx mdls =
  let rec fold loaded ctx = function
    | [] ->
       let loaded = List.rev loaded in
       (ctx, locate (Dsyntax.MLModules loaded) loc)
    | mdl_name :: mdls ->
       begin match ml_module ~loc ~basedir ctx mdl_name with
       | ctx, None -> fold loaded ctx mdls
       | ctx, Some (fn, mdl, cmds) ->
          let ctx = Ctx.add_module mdl_name mdl ctx in
          fold ((mdl_name, cmds) :: loaded) ctx mdls
       end
  in
  fold [] ctx mdls

and ml_module ~loc ~basedir ctx mdl_name =
  if Ctx.loaded mdl_name ctx then
    (* We already loaded this module *)
    ctx, None
  else if Ctx.loading mdl_name ctx then
    (* We are in the process of loading this module, circular dependency *)
    error ~loc (CircularRequire (List.rev (mdl_name :: ctx.Ctx.loading)))
  else
    let rec unique xs = function
      | [] -> []
      | y :: ys ->
         let ys = unique (y :: xs) ys in
         if List.mem y xs then ys else y :: ys
    in
    let basename = Name.module_filename mdl_name in
    let fns =
      unique []
        [
          Filename.concat basedir basename ;
        ]
    in
    match List.find_opt Sys.file_exists fns with

    | None ->
       error ~loc (RequiredModuleMissing (mdl_name, fns))

    | Some fn ->
       let ctx = Ctx.push_module mdl_name ctx in
       let ctx, mdl, cmds = load_file ~basedir ctx fn in
       let ctx = Ctx.pop_module ctx in
       ctx, Some (fn, mdl, cmds)


and load_file ~basedir ctx fn =
  let loading = ctx.Ctx.loading in
  let current = ctx.Ctx.current in
  let cmds = Lexer.read_file ?line_limit:None Parser.file fn in
  let ctx = { ctx with Ctx.current = Ctx.empty_module } in
  let ctx, cmds = List.fold_left (fun (ctx,cmds) cmd ->
                      let ctx, cmd = toplevel ~basedir ctx cmd in
                      (ctx, cmd::cmds))
                    (ctx,[]) cmds
  in
  (* pick up the loaded module *)
  let mdl = ctx.Ctx.current in
  (* restore loading and current module *)
  let ctx = { ctx with Ctx.loading=loading; Ctx.current=current } in
  ctx, mdl, List.rev cmds

let file ctx fn =
  let basedir = Filename.dirname fn in
  let ctx, _, cmds = load_file ~basedir ctx fn in
  ctx, cmds
