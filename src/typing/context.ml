(** The typing context *)

(* Type-checking assigns identifiers to types and operations, as these can be
   statically determined. It cannot do so for TT constructors and ML values,
   because they are computed at runtime.

   For the moment we do not assign identifiers to modules because we never
   compare modules.
*)

module SymbolTable :
sig
  type t

  val initial : t

  val add_ml_type : Ident.t * Mlty.ty_def -> t -> t
  val add_ml_operation : Ident.t * (Mlty.ty list * Mlty.ty) -> t -> t
  val add_tt_constructor : Ident.t * Mlty.tt_constructor -> t -> t
  val add_ml_value : Mlty.ty_schema -> t -> t

  val get_ml_type : Path.t -> t -> Ident.t * Mlty.ty_def
  val get_ml_operation : Path.t -> t -> Ident.t * (Mlty.ty list * Mlty.ty)
  val get_tt_constructor : Path.t -> t -> Ident.t * Mlty.tt_constructor
  val get_ml_value : Path.t -> t -> Mlty.ty_schema

  val push_ml_module : t -> t
  val pop_ml_module : t -> t

  val fold_ml_values : ('a -> Mlty.ty_schema -> 'a) -> 'a -> t -> 'a
end =
struct

  module TableMap = Map.Make(
                     struct
                       type t = int
                       let compare = Pervasives.compare
                     end)

  type 'a table = {
      table_map : 'a TableMap.t;
      table_next : int;
    }

  let add info {table_map; table_next} =
    { table_map = TableMap.add table_next info table_map ;
      table_next = table_next + 1 }

  let get k {table_map; _} = TableMap.find k table_map

  let get_last {table_map; table_next} = TableMap.find (table_next - 1) table_map

  let set_last info ({table_map; table_next} as tbl) =
    { tbl with table_map = TableMap.add (table_next - 1) info tbl.table_map }

  let fold_table f acc {table_map; _} = TableMap.fold (fun _ x acc -> f acc x) table_map acc

  type ml_module = {
      ml_modules : ml_module table;
      ml_types : (Ident.t * Mlty.ty_def) table;
      ml_operations : (Ident.t * (Mlty.ty list * Mlty.ty)) table;
      tt_constructors : (Ident.t * Mlty.tt_constructor) table;
      ml_values : Mlty.ty_schema table;
  }

  let empty_ml_module =
    let empty = { table_map = TableMap.empty; table_next = 0 } in
    { ml_modules = empty;
      ml_types = empty;
      ml_operations = empty;
      tt_constructors = empty;
      ml_values = empty
    }

  type t = {
      top_module : ml_module ;
      current_depth : int;
    }

  let initial =
    { top_module = empty_ml_module;
      current_depth = 0
    }

  let at_current adder tbl =
    let rec update mdl = function

      | 0 -> adder mdl

      | depth ->
         let mdl' = get_last mdl.ml_modules in
         let mdl' = update mdl' (depth-1) in
         { mdl with ml_modules = set_last mdl' mdl.ml_modules }

    in
    { tbl with top_module = update tbl.top_module tbl.current_depth }

  let add_ml_type info =
    at_current (fun mdl -> { mdl with ml_types = add info mdl.ml_types })

  let add_ml_operation info =
    at_current (fun mdl -> { mdl with ml_operations = add info mdl.ml_operations })

  let add_tt_constructor info =
    at_current (fun mdl -> { mdl with tt_constructors = add info mdl.tt_constructors })

  let add_ml_value info =
    at_current (fun mdl -> { mdl with ml_values = add info mdl.ml_values })

  let rec get_path
    : 'a . (Path.level -> ml_module -> 'a) -> Path.t -> t -> 'a
    = fun getter pth tbl ->
    match pth with

    | Path.Direct lvl -> getter lvl tbl.top_module

    | Path.Module (mdl_path, lvl) ->
       let mdl = get_ml_module mdl_path tbl in
       getter lvl mdl

  and get_ml_module pth =
    get_path (fun (Path.Level (_, k)) mdl -> get k mdl.ml_modules) pth

  let get_ml_type =
    get_path (fun (Path.Level (_, k)) mdl -> get k mdl.ml_types)

  let get_ml_operation =
    get_path (fun (Path.Level (_, k)) mdl -> get k mdl.ml_operations)

  let get_tt_constructor =
    get_path (fun (Path.Level (_, k)) mdl -> get k mdl.tt_constructors)

  let get_ml_value =
    get_path (fun (Path.Level (_, k)) mdl -> get k mdl.ml_values)

  let push_ml_module tbl =
    let tbl = at_current (fun mdl -> { mdl with ml_modules = add empty_ml_module mdl.ml_modules }) tbl in
    { tbl with current_depth = tbl.current_depth + 1 }

  let pop_ml_module tbl =
    { tbl with current_depth = tbl.current_depth - 1 }

  let fold_ml_values f x tbl =
    let rec fold x mdl =
      let x = fold_table f x mdl.ml_values in
      fold_table fold x mdl.ml_modules
    in
    fold x tbl.top_module

end

type t = {
    table : SymbolTable.t;
    ml_yield : (Mlty.ty * Mlty.ty) option;
    ml_bound : Mlty.ty_schema list
  }

let empty = {
    table = SymbolTable.initial;
    ml_yield = None;
    ml_bound = [];
  }

let lookup_bound (Path.Index (_, k)) {ml_bound;_} =
  let (ps, t) = List.nth ml_bound k in
  let pus = List.map (fun p -> (p, Mlty.fresh_type ())) ps in
  Mlty.instantiate pus t

let lookup_ml_value pth ctx =
  let (ps, t) = SymbolTable.get_ml_value pth ctx.table in
  let pus = List.map (fun p -> (p, Mlty.fresh_type ())) ps in
  Mlty.instantiate pus t

let lookup_ml_operation pth ctx =
  SymbolTable.get_ml_operation pth ctx.table

let lookup_tt_constructor pth ctx =
  SymbolTable.get_tt_constructor pth ctx.table

let lookup_ml_type pth ctx =
  SymbolTable.get_ml_type pth ctx.table

let lookup_ml_type_id pth ctx = fst (lookup_ml_type pth ctx)

let lookup_ml_constructor (t_pth, Path.Level (_, c_lvl)) ctx =
  match lookup_ml_type t_pth ctx with
  | _, Mlty.Alias _ -> assert false
  | _, Mlty.Sum (ps, cs) ->
     let (c', ts) = List.nth cs c_lvl in
     let pus = List.map (fun p -> (p, Mlty.fresh_type ())) ps in
     let ts = List.map (Mlty.instantiate pus) ts
     and out = Mlty.Apply (t_pth, List.map snd pus) in
     (ts, out)

let lookup_continuation {ml_yield;_} =
  match ml_yield with
    | Some cont -> cont
    | None -> assert false

let add_tt_constructor c t ctx =
  let c = Ident.create c in
  { ctx with table = SymbolTable.add_tt_constructor (c,t) ctx.table }

let add_ml_type t d ctx =
  let t = Ident.create t in
  { ctx with table = SymbolTable.add_ml_type (t,d) ctx.table }

let add_ml_operation op opty ctx =
  let op = Ident.create op in
  { ctx with table = SymbolTable.add_ml_operation (op,opty) ctx.table }

let add_ml_value _name schema ctx =
  { ctx with table = SymbolTable.add_ml_value schema ctx.table }

let op_cases op ~output ctx =
  let (oid, (args, opout)) = lookup_ml_operation op ctx in
  oid, args, { ctx with ml_yield = Some (opout, output) }

let unfold ctx t_pth ts =
  match lookup_ml_type t_pth ctx with
    | _, Mlty.Sum _ -> None
    | _, Mlty.Alias (ps, t) ->
       let pus = List.combine ps ts in
       Some (Mlty.instantiate pus t)

let push_ml_module ctx = { ctx with table = SymbolTable.push_ml_module ctx.table }

let pop_ml_module ctx = { ctx with table = SymbolTable.pop_ml_module ctx.table }

let gather_known s ctx =
  let subst = Substitution.apply s in
  let known =
    SymbolTable.fold_ml_values
      (fun known (_, t) -> Mlty.MetaSet.union known (Mlty.occuring (subst t)))
      Mlty.MetaSet.empty
      ctx.table
  in
  let known = match ctx.ml_yield with
    | Some (t1, t2) ->
       Mlty.MetaSet.union known (Mlty.MetaSet.union (Mlty.occuring (subst t1)) (Mlty.occuring (subst t2)))
    | None -> known
  in
  known
