(** Conversion from sugared to desugared input syntax. The responsibilities of
   this phase is to:

    * resolve all names to levels and indices

    * check arities of constructors and operations

    We check arities here in order to figure out how to split a spine [C e1 ... en]
    into an application of a constructor [(C e1 ... ek) ... en] where [k] is
    the arity of [C].
*)

(** Arity of an operator *)
type arity = int

(** Information about names *)
type info =
  | Bound of Path.index
  | Value of Path.t
  | TTConstructor of Path.t * arity
  | MLConstructor of Path.ml_constructor * arity
  | Operation of Path.t * arity

let print_info info ppf = match info with
  | Bound _ | Value _ -> Format.fprintf ppf "a value"
  | TTConstructor _ -> Format.fprintf ppf "a constructor"
  | MLConstructor _ -> Format.fprintf ppf "an ML constructor"
  | Operation _ -> Format.fprintf ppf "an operation"

type error =
  | UnknownPath of Name.path
  | UnknownType of Name.path
  | NameAlreadyDeclared of Name.t * info
  | MLTypeAlreadyDeclared of Name.t
  | OperationExpected : Name.path * info -> error
  | InvalidTermPatternName : Name.path * info -> error
  | InvalidPatternName : Name.t * info -> error
  | InvalidAppliedPatternName : Name.path * info -> error
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

  | InvalidTermPatternName (pth, info) ->
     Format.fprintf ppf "%t cannot be used in a term pattern as it is %t"
       (Name.print_path pth)
       (print_info info)

  | InvalidPatternName (x, info) ->
     Format.fprintf ppf "%t cannot be used in a pattern as it is %t"
       (Name.print x)
       (print_info info)

  | InvalidAppliedPatternName (pth, info) ->
     Format.fprintf ppf "%t cannot be applied in a pattern as it is %t"
       (Name.print_path pth)
       (print_info info)

  | NonlinearPattern x ->
     Format.fprintf ppf "non-linear pattern variable %t is not allowed."
       (Name.print x)

  | ArityMismatch (pth, used, expected) ->
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
        (Print.sequence (Name.print ~parentheses:false) "," mdls)

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

module Ctx = struct

  (* For each type construct we store its arity, and possibly the constructors with their arities *)
  type ml_type_info = arity * arity Name.AssocLevel.t option

  (* A module has two name spaces, one for ML types and the other for everything
     else. However, we keep operations, TT constructors and values in separate
     lists because we need to compute their indices. All entities are accessed
     by de Bruijn levels, and shadowing is forbidden. *)
  type ml_module = {
      ml_types : ml_type_info Name.AssocLevel.t ;
      ml_operations : arity Name.AssocLevel.t ;
      tt_constructors : arity Name.AssocLevel.t ;
      ml_values : unit Name.AssocLevel.t
    }

  type t = {
      (* Known ML modules *)
      ml_modules : ml_module Name.AssocLevel.t;
      (* Current module, here values are accessed by de Bruijn indices *)
      current_ml_types : ml_type_info Name.AssocLevel.t ;
      current_ml_operations : arity Name.AssocLevel.t ;
      current_tt_constructors : arity Name.AssocLevel.t ;
      current_ml_values : unit Name.AssocIndex.t ; (* this one is by index *)
      (* Is a continuation available? *)
      yield : bool ;
      (* Chain of modules being loaded (for dependency cycle detection) *)
      loading : Name.t list;
    }

  let empty = {
      ml_modules = Name.AssocLevel.empty ;
      current_ml_types = Name.AssocLevel.empty ;
      current_ml_operations = Name.AssocLevel.empty ;
      current_tt_constructors = Name.AssocLevel.empty ;
      current_ml_values = Name.AssocIndex.empty;
      yield = false;
      loading = []
    }

  (* Lookup functions named [find_XYZ] return optional results,
     while those named [get_XYZ] require a location and either return
     a result or trigger an error. *)

  let find_module mdl_name ctx = Name.AssocLevel.find mdl_name ctx.ml_modules

  (* Find an ML constructor in a list of ML type definitions *)
  let find_ml_constructor x lst =
    let rec search t_lvl = function
      | [] -> None
      | (_, (_, None)) :: css -> search (t_lvl+1) css
      | (t, (_, Some cs)) :: css ->
         begin match Name.AssocLevel.find x cs with
         | None -> search (t_lvl+1) css
         | Some (arity, x_lvl) -> Some (Path.Level (t, t_lvl), Path.Level (x, x_lvl), arity)
         end
    in
    search 0 (Name.AssocLevel.to_list lst)

  let find_ml_type pth ctx =
    match pth with

    | Name.PName t ->
       begin match Name.AssocLevel.find t ctx.current_ml_types with
       | Some (_, l) -> Some (Path.Direct (Path.Level (t, l)))
       | None -> None
       end

    | Name.PModule (mdl_name, t) ->
       begin match find_module mdl_name ctx with
       | Some (mdl, mdl_lvl) ->
          begin match Name.AssocLevel.find t mdl.ml_types with
          | Some (_, t_lvl) -> Some (Path.Module (Path.Level (mdl_name, mdl_lvl), Path.Level (t, t_lvl)))
          | None -> None
          end
       | None -> None
       end

  (* Find the information about the given name in the given module. *)
  let find_in_module x mdl_lvl mdl =
    match Name.AssocLevel.find x mdl.ml_values with
    | Some ((), l) -> Some (Value (Path.Module (mdl_lvl, Path.Level (x, l))))
    | None ->
       begin match Name.AssocLevel.find x mdl.tt_constructors with
       | Some (arity, l) -> Some (TTConstructor ((Path.Module (mdl_lvl, Path.Level (x, l))), arity))
       | None ->
          begin match Name.AssocLevel.find x mdl.ml_operations with
          | Some (arity, l) -> Some (Operation ((Path.Module (mdl_lvl, Path.Level (x, l)), arity)))
          | None ->
             begin match find_ml_constructor x mdl.ml_types with
             | Some (t_lvl, c_lvl, arity) -> Some (MLConstructor ((Path.Module(mdl_lvl, t_lvl), c_lvl), arity))
             | None -> None
             end
          end
       end

  (* Find the information about the given name in the given module. *)
  let find_in_current x {current_ml_values; current_tt_constructors; current_ml_operations; current_ml_types; _} =
    match Name.AssocIndex.find x current_ml_values with
    | Some ((), i) -> Some (Bound (Path.Index (x, i)))
    | None ->
       begin match Name.AssocLevel.find x current_tt_constructors with
       | Some (arity, l) -> Some (TTConstructor ((Path.Direct (Path.Level (x, l))), arity))
       | None ->
          begin match Name.AssocLevel.find x current_ml_operations with
          | Some (arity, l) -> Some (Operation ((Path.Direct (Path.Level (x, l)), arity)))
          | None ->
             begin match find_ml_constructor x current_ml_types with
             | Some (t_lvl, c_lvl, arity) -> Some (MLConstructor ((Path.Direct t_lvl, c_lvl), arity))
             | None -> None
             end
          end
       end

  (* Find the information about the given path *)
  let find_info_path pth ctx =
    match pth with

    | Name.PName x ->
       (* lookup in the current module *)
       find_in_current x ctx

    | Name.PModule (mdl_name, x) ->
       begin match find_module mdl_name ctx with
         | None -> None
         | Some (mdl, mdl_lvl) ->
            let lvl = Path.Level (mdl_name, mdl_lvl) in
            find_in_module x lvl mdl
       end

  (* Check that the name is not bound already *)
  let check_is_fresh_name ~loc x ctx =
    match find_in_current x ctx with
    | None -> ()
    | Some info -> error ~loc (NameAlreadyDeclared (x, info))

  (* Check that the type is not bound already *)
  let check_is_fresh_type ~loc x ctx =
    match Name.AssocLevel.find x ctx.current_ml_types with
    | None -> ()
    | Some _ -> error ~loc (MLTypeAlreadyDeclared x)

  (* Get the info about a path, or fail *)
  let get_info_path ~loc pth ctx =
    match find_info_path pth ctx with
    | None -> error ~loc (UnknownPath pth)
    | Some info -> info

  (* Get information about the list empty list constructor *)
  let get_path_nil ctx =
    match find_in_current Name.Predefined.nil ctx with
    | Some (MLConstructor (pth, 0)) -> pth
    | None |Some (Bound _ | Value _ | MLConstructor _ | TTConstructor _ | Operation _) ->
       assert false

  let get_path_cons ctx =
    match find_in_current Name.Predefined.cons ctx with
    | Some (MLConstructor (pth, 2)) -> pth
    | None |Some (Bound _ | Value _ | MLConstructor _ | TTConstructor _ | Operation _) ->
       assert false

  (* Get information about the empty list constructor *)
  let get_path_nil ctx =
    match find_in_current Name.Predefined.nil ctx with
    | Some (MLConstructor (pth, 0)) -> pth
    | None |Some (Bound _ | Value _ | MLConstructor _ | TTConstructor _ | Operation _) ->
       assert false

  (* Get information about the cons list constructor *)
  let get_path_cons ctx =
    match find_in_current Name.Predefined.cons ctx with
    | Some (MLConstructor (pth, 2)) -> pth
    | None |Some (Bound _ | Value _ | MLConstructor _ | TTConstructor _ | Operation _) ->
       assert false

  (* Get the arity and de Bruijn level of type named [t] and its definition *)
  let get_ml_type ~loc pth ctx =
    match find_ml_type pth ctx with
    | None -> error ~loc (UnknownType pth)
    | Some info -> info

  (* Make yield available. (It can never be made unavailable, it seems) *)
  let set_yield ctx = { ctx with yield = true }

  (* Is yield allowed? *)
  let check_yield ~loc ctx =
    if not ctx.yield then error ~loc UnboundYield

  (* Add a module to the module list. *)
  let add_module mdl_name mdl ctx =
    { ctx with ml_modules =  Name.AssocLevel.add mdl_name mdl ctx.ml_modules }

  (* Add a local bound value. If [~fresh] is given, shadowing is prevented. *)
  let add_bound ?(fresh=None) x ctx =
    begin match fresh with
    | None -> ()
    | Some loc -> check_is_fresh_name ~loc x ctx
    end ;
    { ctx with current_ml_values = Name.AssocIndex.add x () ctx.current_ml_values }

  (* Add a TT constructor of given arity *)
  let add_tt_constructor ~loc c arity ctx =
    check_is_fresh_name ~loc c ctx ;
    { ctx with current_tt_constructors =  Name.AssocLevel.add c arity ctx.current_tt_constructors }

  (* Add an operation of given arity *)
  let add_operation ~loc op arity ctx =
    check_is_fresh_name ~loc op ctx ;
    { ctx with current_ml_operations =  Name.AssocLevel.add op arity ctx.current_ml_operations }

  (* Add to the context the fact that [t] is a type constructor with given constructors and arities. *)
  let add_ml_type ~loc t cs ctx  =
    check_is_fresh_type ~loc t ctx ;
    { ctx with current_ml_types = Name.AssocLevel.add t cs ctx.current_ml_types }

  (* Has the given file already been loaded? *)
  let loaded mdl {ml_modules; _} =
    match Name.AssocLevel.find mdl ml_modules with
    | None -> false
    | Some _ -> true

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

  (* Check that the arity is the expected one. *)
  let check_arity ~loc pth used expected =
    if used <> expected then
      error ~loc (ArityMismatch (pth, used, expected))

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

         | Name.PModule _ ->
                let pth  = Ctx.get_ml_type ~loc pth ctx in
                let args = List.map mlty args in
                Dsyntax.ML_Apply (pth, args)

         | Name.PName x ->
            (* It could be one of the bound type parameters *)
            let rec search k = function
              | [] ->
              (* It's a type name *)
              begin
                let pth  = Ctx.get_ml_type ~loc pth ctx in
                let args = List.map mlty args in
                Dsyntax.ML_Apply (pth, args)
              end
              | None :: lst -> search k lst
              | Some y :: lst ->
                 if Name.equal x y then
                   (* It's a type parameter *)
                   begin match args with
                   | [] -> Dsyntax.ML_Bound (Path.Index (x, k))
                   | _::_ -> error ~loc AppliedTyParam
                   end
                 else search (k+1) params
            in
            search 0 params
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
     let ctx = Ctx.add_bound x ctx in
     ctx, (locate (Dsyntax.Patt_TT_Var x) loc)

  | Input.Patt_TT_As (p1, p2) ->
     let ctx, p1 = tt_pattern ctx p1 in
     let ctx, p2 = tt_pattern ctx p2 in
     ctx, locate (Dsyntax.Patt_TT_As (p1, p2)) loc

  | Input.Patt_TT_Constructor (c, ps) ->
     begin match Ctx.get_info_path ~loc c ctx with
     | TTConstructor (pth, arity) ->
        check_arity ~loc c (List.length ps) arity ;
        pattern_tt_constructor ~loc ctx pth ps
     | (MLConstructor _ | Operation _ | Value _ | Bound _) as info ->
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
                 let ctx = Ctx.add_bound x ctx in
                 ctx, Some x
              | None -> ctx, None
            end
          in
          let ctx, p = fold ctx abstr in
          ctx, locate (Dsyntax.Patt_TT_Abstraction (xopt, popt,p)) loc
     in
     fold ctx abstr

and pattern_tt_constructor ~loc ctx pth ps =
  let rec fold ctx ps = function
    | [] ->
       let ps = List.rev ps in
       ctx, locate (Dsyntax.Patt_TT_Constructor (pth, ps)) loc
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
     begin match Ctx.find_in_current x ctx with

     | Some (Bound _ | Value _) (* we allow shadowing of named values *)
     | None ->
        let ctx = Ctx.add_bound x ctx in
        ctx, locate (Dsyntax.Patt_Var x) loc

     | Some (MLConstructor (pth, arity)) ->
        check_arity ~loc (Name.path_direct x) 0 arity ;
        ctx, locate (Dsyntax.Patt_Constructor (pth, [])) loc

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

  | Input.Patt_Constructor (c, ps) ->
     begin match Ctx.get_info_path ~loc c ctx with
     | MLConstructor (pth, arity) ->
        check_arity ~loc c (List.length ps) arity ;
        let rec fold ctx ps = function
          | [] ->
             let ps = List.rev ps in
             ctx, locate (Dsyntax.Patt_Constructor (pth, ps)) loc
          | p::rem ->
             let ctx, p = pattern ctx p in
             fold ctx (p::ps) rem
        in
        fold ctx [] ps

     | (Bound _ | Value _ | TTConstructor _ | Operation _) as info ->
        error ~loc (InvalidAppliedPatternName (c, info))
     end

  | Input.Patt_List ps ->
     let nil_path = Ctx.get_path_nil ctx
     and cons_path = Ctx.get_path_cons ctx in
     let rec fold ~loc ctx = function
       | [] -> ctx, locate (Dsyntax.Patt_Constructor (nil_path, [])) loc
       | p :: ps ->
          let ctx, p = pattern ctx  p in
          let ctx, ps = fold ~loc:(p.Location.loc) ctx ps in
          ctx, locate (Dsyntax.Patt_Constructor (cons_path, [p ; ps])) loc
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
     if Name.set_mem x forbidden then
       error ~loc (NonlinearPattern x)
     else
       Name.set_add x forbidden

let rec check_linear_tt ?(forbidden=Name.set_empty) {Location.thing=p';loc} =
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


let rec check_linear ?(forbidden=Name.set_empty) {Location.thing=p';loc} =
  match p' with

  | Input.Patt_Anonymous -> forbidden

  | Input.Patt_Var x ->
     check_linear_pattern_variable ~loc ~forbidden x

  | Input.Patt_As (p1, p2) ->
     let forbidden = check_linear ~forbidden p1 in
     check_linear ~forbidden p2

  | Input.Patt_Judgement pt ->
     check_linear_tt ~forbidden pt

  | Input.Patt_Constructor (_, ps)
  | Input.Patt_List ps
  | Input.Patt_Tuple ps ->
     check_linear_list ~forbidden ps

and check_linear_list ~forbidden = function
  | [] -> forbidden
  | p :: ps ->
     let forbidden = check_linear ~forbidden p in
     check_linear_list ~forbidden ps

let rec comp ctx {Location.thing=c';loc} =
  match c' with
  | Input.Handle (c, hcs) ->
     let c = comp ctx c
     and h = handler ~loc ctx hcs in
     locate (Dsyntax.With (h, c)) loc

  | Input.With (c1, c2) ->
     let c1 = comp ctx c1
     and c2 = comp ctx c2 in
     locate (Dsyntax.With (c1, c2)) loc

  | Input.Let (lst, c) ->
     let ctx, lst = let_clauses ~loc ~toplevel:false ctx lst in
     let c = comp ctx c in
     locate (Dsyntax.Let (lst, c)) loc

  | Input.LetRec (lst, c) ->
     let ctx, lst = letrec_clauses ~loc ~toplevel:false ctx lst in
     let c = comp ctx c in
     locate (Dsyntax.LetRec (lst, c)) loc

  | Input.MLAscribe (c, sch) ->
     let c = comp ctx c in
     let sch = ml_schema ctx sch in
     locate (Dsyntax.MLAscribe (c, sch)) loc

  | Input.Now (x,c1,c2) ->
     let x = comp ctx x
     and c1 = comp ctx c1
     and c2 = comp ctx c2 in
     locate (Dsyntax.Now (x,c1,c2)) loc

  | Input.Current c ->
     let c = comp ctx c in
     locate (Dsyntax.Current c) loc

  | Input.Lookup c ->
     let c = comp ctx c in
     locate (Dsyntax.Lookup c) loc

  | Input.Ref c ->
     let c = comp ctx c in
     locate (Dsyntax.Ref c) loc

  | Input.Update (c1, c2) ->
     let c1 = comp ctx c1
     and c2 = comp ctx c2 in
     locate (Dsyntax.Update (c1, c2)) loc

  | Input.Sequence (c1, c2) ->
     let c1 = comp ctx c1
     and c2 = comp ctx c2 in
     locate (Dsyntax.Sequence (c1, c2)) loc


  | Input.Assume ((xopt, t), c) ->
     let t = comp ctx t in
     let ctx = (match xopt with None -> ctx | Some x -> Ctx.add_bound x ctx) in
     let c = comp ctx c in
     locate (Dsyntax.Assume ((xopt, t), c)) loc

  | Input.Match (c, cases) ->
     let c = comp ctx c
     and cases = List.map (match_case ctx) cases in
     locate (Dsyntax.Match (c, cases)) loc

  | Input.Ascribe (c, t) ->
     let t = comp ctx t
     and c = comp ctx c in
     locate (Dsyntax.Ascribe (c, t)) loc


  | Input.Abstract (xs, c) ->
     let rec fold ctx ys = function
       | [] ->
          let c = comp ctx c in
          mk_abstract ~loc ys c
       | (x, None) :: xs ->
          let ctx = Ctx.add_bound x ctx
          and ys = (x, None) :: ys in
          fold ctx ys xs
       | (x, Some t) :: xs ->
          let ys = (let t = comp ctx t in (x, Some t) :: ys)
          and ctx = Ctx.add_bound x ctx in
          fold ctx ys xs
     in
     fold ctx [] xs

  | Input.Substitute (e, cs) ->
     let e = comp ctx e in
     List.fold_left
       (fun e c ->
          let c = comp ctx c
          and loc = Location.from_to loc c.Location.loc in

          locate (Dsyntax.Substitute (e, c)) loc)
       e cs

  | Input.Spine (e, cs) ->
     spine ctx e cs

  | Input.Var x ->

     begin match Ctx.get_info_path ~loc x ctx with

     | Bound i -> locate (Dsyntax.Bound i) loc

     | Value pth -> locate (Dsyntax.Value pth) loc

     | TTConstructor (pth, arity) ->
        check_arity ~loc x 0 arity ;
        locate (Dsyntax.TTConstructor (pth, [])) loc

     | MLConstructor (pth, arity) ->
        check_arity ~loc x 0 arity ;
        locate (Dsyntax.MLConstructor (pth, [])) loc

     | Operation (pth, arity) ->
        check_arity ~loc x 0 arity ;
        locate (Dsyntax.Operation (pth, [])) loc
     end

  | Input.Yield c ->
     Ctx.check_yield ~loc ctx ;
     let c = comp ctx c in
     locate (Dsyntax.Yield c) loc

  | Input.Function (xs, c) ->
     let rec fold ctx = function
       | [] -> comp ctx c
       | (x, t) :: xs ->
          let ctx = Ctx.add_bound x ctx in
          let c = fold ctx xs in
          let t = arg_annotation ctx t in
          locate (Dsyntax.Function (x, t, c)) loc
     in
     fold ctx xs

  | Input.Handler hcs ->
     handler ~loc ctx hcs

  | Input.List cs ->
     let nil_path = Ctx.get_path_nil ctx
     and cons_path = Ctx.get_path_cons ctx in
     let rec fold ~loc = function
       | [] -> locate (Dsyntax.MLConstructor (nil_path, [])) loc
       | c :: cs ->
          let c = comp ctx c in
          let cs = fold ~loc:(c.Location.loc) cs in
          locate (Dsyntax.MLConstructor (cons_path, [c ; cs])) loc
     in
     fold ~loc cs

  | Input.Tuple cs ->
     let lst = List.map (comp ctx) cs in
     locate (Dsyntax.Tuple lst) loc

  | Input.String s ->
     locate (Dsyntax.String s) loc

  | Input.Context c ->
     let c = comp ctx c in
     locate (Dsyntax.Context c) loc

  | Input.Occurs (c1,c2) ->
     let c1 = comp ctx c1
     and c2 = comp ctx c2 in
     locate (Dsyntax.Occurs (c1,c2)) loc

  | Input.Natural c ->
     let c = comp ctx c in
     locate (Dsyntax.Natural c) loc

  | Input.Open (mdl, c) ->
     failwith "modules not implemented"

and let_clauses ~loc ~toplevel ctx lst =
  let fresh = if toplevel then Some loc else None in
  let rec fold ctx' lst' = function
    | [] ->
       let lst' = List.rev lst' in
       ctx', lst'

    | Input.Let_clause_ML (xys_opt, sch, c) :: clauses ->
       let ys = (match xys_opt with None -> [] | Some (_, ys) -> ys) in
       let c = let_clause ~loc ~fresh ctx ys c in
       let sch = let_annotation ctx sch in
       let x, ctx' =
         begin match xys_opt with
         | None -> locate Dsyntax.Patt_Anonymous loc, ctx'
         (* XXX if x carried its location, we would use it here *)
         | Some (x, _) -> locate (Dsyntax.Patt_Var x) loc, Ctx.add_bound ~fresh x ctx'
         end
       in
       let lst' = Dsyntax.Let_clause (x, sch, c) :: lst' in
       fold ctx' lst' clauses

    | Input.Let_clause_tt (xopt, t, c) :: clauses ->
       let c = let_clause_tt ctx c t in
       let sch = Dsyntax.Let_annot_none in
       let x, ctx' =
         begin match xopt with
         | None -> locate Dsyntax.Patt_Anonymous loc, ctx'
         (* XXX if x carried its location, we would use it here *)
         | Some x -> locate (Dsyntax.Patt_Var x) loc, Ctx.add_bound ~fresh x ctx'
         end
       in
       let lst' = Dsyntax.Let_clause (x, sch, c) :: lst' in
       fold ctx' lst' clauses

    | Input.Let_clause_patt (pt, sch, c) :: clauses ->
       let c = comp ctx c in
       let sch = let_annotation ctx sch in
       let ctx', pt = pattern ctx' pt in
       let lst' = Dsyntax.Let_clause (pt, sch, c) :: lst' in

     fold ctx' lst' clauses
  in
  let rec check_unique forbidden = function
    | [] -> ()
    | Input.Let_clause_ML (Some (x, _), _, _) :: lst
    | Input.Let_clause_tt (Some x, _, _) :: lst ->
       if Name.set_mem x forbidden
       then error ~loc (ParallelShadowing x)
       else check_unique (Name.set_add x forbidden) lst
    | Input.Let_clause_ML (None, _, _) :: lst
    | Input.Let_clause_tt (None, _, _) :: lst ->
       check_unique forbidden lst
    | Input.Let_clause_patt (pt, _, _) :: lst ->
       let forbidden = check_linear ~forbidden pt in
       check_unique forbidden lst
  in
  check_unique Name.set_empty lst ;
  fold ctx [] lst

and letrec_clauses ~loc ~toplevel ctx lst =
  let fresh = if toplevel then Some loc else None in
  let ctx =
    List.fold_left (fun ctx (f, _, _, _, _) -> Ctx.add_bound ~fresh f ctx) ctx lst
  in
  let rec fold lst' = function
    | [] ->
       let lst' = List.rev lst' in
       ctx, lst'
    | (f, yt, ys, sch, c) :: xcs ->
       if List.exists (fun (g, _, _, _, _) -> Name.equal f g) xcs
       then
         error ~loc (ParallelShadowing f)
       else
         let yt, c = letrec_clause ~loc ~fresh ctx yt ys c in
         let sch = let_annotation ctx sch in
         let lst' = Dsyntax.Letrec_clause (f, yt, sch, c) :: lst' in
         fold lst' xcs
  in
  fold [] lst

and let_clause ~loc ~fresh ctx ys c =
  let rec fold ctx = function
    | [] ->
       comp ctx c
    | (y, t) :: ys ->
       let ctx = Ctx.add_bound ~fresh y ctx in
       let c = fold ctx ys in
       let t = arg_annotation ctx t in
       locate (Dsyntax.Function (y, t, c)) (c.Location.loc) (* XXX improve location *)
  in
  fold ctx ys

and let_clause_tt ctx c t =
  let c = comp ctx c
  and t = comp ctx t in
  locate (Dsyntax.Ascribe (c, t)) (c.Location.loc)

and letrec_clause ~loc ~fresh ctx (y, t) ys c =
  let t = arg_annotation ctx t in
  let ctx = Ctx.add_bound ~fresh y ctx in
  let c = let_clause ~loc ~fresh ctx ys c in
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
and spine ctx ({Location.thing=c';loc} as c) cs =

  (* Auxiliary function which splits a list into two parts with k
     elements in the first part. *)
  let split_at constr arity lst =
    let rec split acc m lst =
      if m = 0 then
        List.rev acc, lst
      else
        match lst with
        | [] -> error ~loc (ArityMismatch (constr, List.length acc, arity))
        | x :: lst -> split (x :: acc) (m - 1) lst
    in
    split [] arity lst
  in

  (* First we calculate the head of the spine, and the remaining arguments. *)
  let head, cs =
    match c' with

    | Input.Var x ->
       begin match Ctx.get_info_path ~loc x ctx with

       | Bound i ->
          locate (Dsyntax.Bound i) loc, cs

       | Value pth ->
          locate (Dsyntax.Value pth) loc, cs

       | TTConstructor (pth, arity) ->
          let cs', cs = split_at x arity cs in
          tt_constructor ~loc ctx pth cs', cs

       | MLConstructor (pth, arity) ->
          let cs', cs = split_at x arity cs in
          ml_constructor ~loc ctx pth cs', cs

       | Operation (pth, arity) ->
          let cs', cs = split_at x arity cs in
          operation ~loc ctx pth cs', cs

       end

    | _ -> comp ctx c, cs
  in

  (* TODO improve locs *)
  List.fold_left
    (fun head arg ->
       let arg = comp ctx arg
       and loc = Location.union loc arg.Location.loc in
       let head = Dsyntax.Apply (head, arg) in
       locate head loc)
    head
    cs

(* Desugar handler cases. *)
and handler ~loc ctx hcs =
  (* for every case | op p => c we do op binder => match binder with | p => c end *)
  let rec fold val_cases op_cases finally_cases = function
    | [] ->
       List.rev val_cases,
       List.map (fun (op, cs) -> (op, List.rev cs)) op_cases,
       List.rev finally_cases

    | Input.CaseVal c :: hcs ->
       (* XXX if this handler is in a outer handler's operation case, should we use its yield?
          eg handle ... with | op => handler | val x => yield x end end *)
       let case = match_case ctx c in
       fold (case::val_cases) op_cases finally_cases hcs

    | Input.CaseOp (op, ((ps,_,_) as c)) :: hcs ->

       begin match Ctx.get_info_path ~loc op ctx with

       | Operation (pth, arity) ->
          check_arity ~loc op (List.length ps) arity ;
          let case = match_op_case (Ctx.set_yield ctx) c in
          let my_cases = try List.assoc pth op_cases with Not_found -> [] in
          let my_cases = case::my_cases in
          fold val_cases ((pth, my_cases) :: op_cases) finally_cases hcs

       | (Bound _ | Value _ | TTConstructor _ | MLConstructor _) as info ->
          error ~loc (OperationExpected (op, info))

       end

    | Input.CaseFinally c :: hcs ->
       let case = match_case ctx c in
       fold val_cases op_cases (case::finally_cases) hcs

  in
  let handler_val, handler_ops, handler_finally = fold [] [] [] hcs in
  locate (Dsyntax.Handler (Dsyntax.{ handler_val ; handler_ops ; handler_finally })) loc

(* Desugar a match case *)
and match_case ctx (p, g, c) =
  ignore (check_linear p) ;
  let ctx, p = pattern ctx p in
  let g = when_guard ctx g
  and c = comp ctx c in
  (p, g, c)

and when_guard ctx = function
  | None -> None
  | Some c ->
     let c = comp ctx c in
     Some c

and match_op_case ctx (ps, pt, c) =
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
       let c = comp ctx c in
       (qs, pt, c)

    | p :: ps ->
       let ctx, q = pattern ctx p in
       fold ctx (q :: qs) ps
  in
  fold ctx [] ps

and ml_constructor ~loc ctx x cs =
  let cs = List.map (comp ctx) cs in
  locate (Dsyntax.MLConstructor (x, cs)) loc

and tt_constructor ~loc ctx pth cs =
  let cs = List.map (comp ctx) cs in
  locate (Dsyntax.TTConstructor (pth, cs)) loc

and operation ~loc ctx x cs =
  let cs = List.map (comp ctx) cs in
  locate (Dsyntax.Operation (x, cs)) loc

let decl_operation ~loc ctx args res =
  let args = List.map (mlty ctx []) args
  and res = mlty ctx [] res in
  args, res

let mlty_def ~loc ctx params = function

  | Input.ML_Alias ty ->
     let ty = mlty ctx params ty in
     Dsyntax.ML_Alias ty

  | Input.ML_Sum lst ->
     let lst = List.map (fun (c, args) -> (c, List.map (mlty ctx params) args)) lst in
     Dsyntax.ML_Sum lst

let mlty_info params = function

  | Input.ML_Alias _ -> (List.length params), None

  | Input.ML_Sum lst ->
     let cs =
       List.fold_left
         (fun cs (c, args) -> Name.AssocLevel.add c (List.length args) cs)
         Name.AssocLevel.empty
         lst
     in
     (List.length params),
     Some cs

let mlty_defs ~loc ctx defs =
  (* we process the definitions and the context in parallel *)
  let defs =
    List.map (fun (t, (params, def)) -> (t, (params, mlty_def ~loc ctx params def))) defs
  and ctx =
    List.fold_left
      (fun ctx (t, (params, def)) -> Ctx.add_ml_type ~loc t (mlty_info params def) ctx)
      ctx defs
  in
  ctx, defs

let mlty_rec_defs ~loc ctx defs =
  (* first change the context  *)
  let ctx =
    List.fold_left
      (fun ctx (t, (param, def)) -> Ctx.add_ml_type ~loc t (mlty_info param def) ctx)
      ctx defs
  in
  (* check for parallel shadowing *)
  let check_shadow = function
    | [] -> ()
    | (t, _) :: defs ->
       if List.exists (fun (t', _) -> Name.equal t t') defs then
         error ~loc (ParallelShadowing t)
  in
  check_shadow defs ;
  let defs =
    List.map (fun (t, (params, def)) -> (t, (params, mlty_def ~loc ctx params def))) defs in
  ctx, defs

let local_context ctx xcs m =
  let rec fold ctx xcs_out = function
    | [] ->
       let xcs_out = List.rev xcs_out in
       let v = m ctx in
       v, xcs_out
    | (x, c) :: xcs ->
       let c = comp ctx c in
       let ctx = Ctx.add_bound x ctx in
       fold ctx ((x,c) :: xcs_out) xcs
  in
  fold ctx [] xcs

let premise ctx {Location.thing=prem;loc} =
  match prem with
  | Input.PremiseIsType (mvar, local_ctx) ->
     let (), local_ctx = local_context ctx local_ctx (fun _ -> ()) in
     let ctx = (match mvar with None -> ctx | Some x -> Ctx.add_bound x ctx) in
     ctx, locate (Dsyntax.PremiseIsType (mvar, local_ctx)) loc

  | Input.PremiseIsTerm (mvar, local_ctx, c) ->
     let c, local_ctx =
       local_context
         ctx local_ctx
         (fun ctx -> comp ctx c)
     in
     let ctx = (match mvar with None -> ctx | Some x -> Ctx.add_bound x ctx) in
     ctx, locate (Dsyntax.PremiseIsTerm (mvar, local_ctx, c)) loc

  | Input.PremiseEqType (mvar, local_ctx, (c1, c2)) ->
     let c12, local_ctx =
       local_context
         ctx local_ctx
         (fun ctx ->
           comp ctx c1,
           comp ctx c2)
     in
     let ctx = (match mvar with None -> ctx | Some x -> Ctx.add_bound x ctx) in
     ctx, locate (Dsyntax.PremiseEqType (mvar, local_ctx, c12)) loc

  | Input.PremiseEqTerm (mvar, local_ctx, (c1, c2, c3)) ->
     let c123, local_ctx =
       local_context ctx local_ctx
       (fun ctx ->
         comp ctx c1,
         comp ctx c2,
         comp ctx c3)
     in
     let ctx = (match mvar with None -> ctx | Some x -> Ctx.add_bound x ctx) in
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
         (fun ctx -> comp ctx c)
     in
     let ctx = Ctx.add_tt_constructor ~loc rname (List.length prems) ctx in
     (ctx, locate (Dsyntax.RuleIsTerm (rname, prems, c)) loc)

  | Input.RuleEqType (rname, prems, (c1, c2)) ->
     let c12, prems =
       premises
         ctx prems
         (fun ctx ->
           comp ctx c1,
           comp ctx c2)
     in
     let ctx = Ctx.add_tt_constructor ~loc rname (List.length prems) ctx in
     (ctx, locate (Dsyntax.RuleEqType (rname, prems, c12)) loc)

  | Input.RuleEqTerm (rname, prems, (c1, c2, c3)) ->
     let c123, prems =
       premises
         ctx prems
         (fun ctx ->
          comp ctx c1,
          comp ctx c2,
          comp ctx c3)
     in
     let ctx = Ctx.add_tt_constructor ~loc rname (List.length prems) ctx in
     (ctx, locate (Dsyntax.RuleEqTerm (rname, prems, c123)) loc)

  | Input.DeclOperation (op, (args, res)) ->
     let args, res = decl_operation ~loc ctx args res in
     let ctx = Ctx.add_operation ~loc op (List.length args) ctx in
     (ctx, locate (Dsyntax.DeclOperation (op, (args, res))) loc)

  | Input.DefMLType defs ->
     let ctx, defs = mlty_defs ~loc ctx defs in
     (ctx, locate (Dsyntax.DefMLType defs) loc)

  | Input.DefMLTypeRec defs ->
     let ctx, defs = mlty_rec_defs ~loc ctx defs in
     (ctx, locate (Dsyntax.DefMLTypeRec defs) loc)

  | Input.DeclExternal (x, sch, s) ->
     let sch = ml_schema ctx sch in
     let ctx = Ctx.add_bound x ctx in
     (ctx, locate (Dsyntax.DeclExternal (x, sch, s)) loc)

  | Input.TopLet lst ->
     let ctx, lst = let_clauses ~loc ~toplevel:true ctx lst in
     (ctx, locate (Dsyntax.TopLet lst) loc)

  | Input.TopLetRec lst ->
     let ctx, lst = letrec_clauses ~loc ~toplevel:true ctx lst in
     (ctx, locate (Dsyntax.TopLetRec lst) loc)

  | Input.TopComputation c ->
     let c = comp ctx c in
     (ctx, locate (Dsyntax.TopComputation c) loc)

  | Input.TopDynamic (x, annot, c) ->
     let c = comp ctx c in
     let ctx = Ctx.add_bound x ctx in
     let annot = arg_annotation ctx annot in
     (ctx, locate (Dsyntax.TopDynamic (x, annot, c)) loc)

  | Input.TopNow (x, c) ->
     let x = comp ctx x in
     let c = comp ctx c in
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
  let orig_ctx = ctx in
  let ctx = Ctx.{ empty with
                  ml_modules = orig_ctx.ml_modules;
                  loading = orig_ctx.loading }
  in
  let cmds = Lexer.read_file ?line_limit:None Parser.file fn in
  let ctx, cmds =
    List.fold_left
      (fun (ctx,cmds) cmd ->
        let ctx, cmd = toplevel ~basedir ctx cmd in
        (ctx, cmd::cmds))
      (ctx, [])
      cmds
  in
  (* pick up the loaded module *)
  let mdl = Ctx.{ ml_types = ctx.current_ml_types ;
                  ml_operations = ctx.current_ml_operations ;
                  tt_constructors = ctx.current_tt_constructors ;
                  ml_values = Name.AssocLevel.of_assoc_index ctx.current_ml_values
            }
 in
  (* we might have picked up some new modules *)
  let ctx = Ctx.{ orig_ctx with ml_modules = ctx.ml_modules } in
  ctx, mdl, List.rev cmds

let file ctx fn =
  let basedir = Filename.dirname fn in
  let ctx, _, cmds = load_file ~basedir ctx fn in
  ctx, cmds
