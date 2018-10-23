
module OperationMap = Name.IdentMap

type t = {
  types : (Name.ident * Mlty.ty_def) list; (* types are accessed by De Bruijn level, the name is for printing *)
  variables : (Name.ident * Mlty.ty_schema) list; (* variables are accessed by De Bruijn index, the name is for printing *)
  operations : (Mlty.ty list * Mlty.ty) OperationMap.t;
  tt_constructors : Mlty.tt_constructor_ty Name.IdentMap.t ; (* constructors are accessed by their names *)
  continuation : (Mlty.ty * Mlty.ty) option;
}

let empty = {
  types = [];
  variables = [];
  operations = OperationMap.empty;
  tt_constructors = Name.IdentMap.empty;
  continuation = None;
}

let lookup_var k {variables;_} =
  let _, (ps, t) = List.nth variables k in
  let pus = List.map (fun p -> (p, Mlty.fresh_type ())) ps in
  Mlty.instantiate pus t

let lookup_op op {operations;_} =
  OperationMap.find op operations

let lookup_tt_constructor c {tt_constructors;_} =
  Name.IdentMap.find c tt_constructors

let lookup_aml_constructor c {types;_} =
  let rec fold = function
    | [] -> raise Not_found
    | (_, Mlty.Alias _) :: types -> fold types
    | (x, Mlty.Sum (ps, constructors)) :: types ->
      let rec search = function
        | [] -> fold types
        | (c', ts) :: _ when Name.eq_ident c c' ->
           let pus = List.map (fun p -> (p, Mlty.fresh_type ())) ps in
           let ts = List.map (Mlty.instantiate pus) ts
           and out = Mlty.App (x, List.length types, List.map snd pus) in
          ts, out
        | _ :: rem -> search rem
      in
      search constructors
  in
  fold types

let lookup_continuation {continuation;_} =
  match continuation with
    | Some cont -> cont
    | None -> assert false

let add_tydef t d ctx =
  let types = (t, d) :: ctx.types in
  {ctx with types}

let add_operation op opty ctx =
  let operations = OperationMap.add op opty ctx.operations in
  {ctx with operations}

let add_let x s ctx =
  let variables = (x, s) :: ctx.variables in
  {ctx with variables}

let op_cases op ~output ctx =
  let (args, opout) = OperationMap.find op ctx.operations in
  let continuation = Some (opout, output) in
  args, {ctx with continuation}

let unfold ctx x ts =
  let _, def = List.nth (List.rev ctx.types) x in
  match def with
    | Mlty.Sum _ -> None
    | Mlty.Alias (ps, t) ->
       let pus = List.combine ps ts in
       Some (Mlty.instantiate pus t)

let gather_known s {variables;continuation;_} =
  let subst = Substitution.apply s in
  let known =
    List.fold_left
      (fun known (_, (_, t)) -> Mlty.MetaSet.union known (Mlty.occuring (subst t)))
      Mlty.MetaSet.empty
      variables
  in
  let known = match continuation with
    | Some (t1, t2) ->
       Mlty.MetaSet.union known (Mlty.MetaSet.union (Mlty.occuring (subst t1)) (Mlty.occuring (subst t2)))
    | None -> known
  in
  known

let predefined_type x ts {types;_} =
  let rec search k = function
    | [] -> assert false
    | (y, _) :: _ when Name.eq_ident x y ->
      Mlty.App (x, k, ts)
    | _ :: types -> search (k + 1) types
  in
  search 0 (List.rev types)

let print_context {variables;_} =
  let penv = Mlty.fresh_penv () in
  List.iter
    (fun (x, sch) ->
      Format.printf
        "%t : %t@\n"
        (Name.print_ident x)
        (Mlty.print_ty_schema ~penv sch)
    )
    variables
