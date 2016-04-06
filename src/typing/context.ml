type constrain =
  | AppConstraint of Location.t * Mlty.ty * Mlty.ty * Mlty.ty

type generalizable =
  | Generalizable
  | Ungeneralizable

let rec generalizable c = match c.Location.thing with
(* yes *)
  | Syntax.Bound _ | Syntax.Function _ | Syntax.Handler _ | Syntax.External _ -> Generalizable
  | Syntax.Constructor (_, cs) | Syntax.Tuple cs ->
    if List.for_all (fun c -> generalizable c = Generalizable) cs
    then Generalizable
    else Ungeneralizable

  | Syntax.Let (_, c) | Syntax.LetRec (_, c) | Syntax.Sequence (_, c) ->
    generalizable c

(* no *)
  | _ -> Ungeneralizable

module OperationMap = Name.IdentMap

type t = {
  types : (Name.ident * Mlty.ty_def) list; (* types are accessed by De Bruijn level, the name is for printing *)
  variables : (Name.ident * Mlty.ty_schema) list; (* variables are accessed by De Bruijn index, the name is for printing *)
  operations : (Mlty.ty list * Mlty.ty) OperationMap.t;
  continuation : (Mlty.ty * Mlty.ty) option;
}

let empty = {
  types = [];
  variables = [];
  operations = OperationMap.empty;
  continuation = None;
}

let lookup_var k {variables;_} =
  let _, (ms, t) = List.nth variables k in
  let s, _ = Substitution.freshen_metas ms in
  Substitution.apply s t

let lookup_op op {operations;_} =
  OperationMap.find op operations

let lookup_constructor c {types;_} =
  let rec fold = function
    | [] -> raise Not_found
    | (_, Mlty.Alias _) :: types -> fold types
    | (x, Mlty.Sum (ms, constructors)) :: types ->
      let rec search = function
        | [] -> fold types
        | (c', ts) :: _ when Name.eq_ident c c' ->
          let s, ms' = Substitution.freshen_metas ms in
          let ts = List.map (Substitution.apply s) ts
          and out = Mlty.App (x, List.length types, List.map (fun m -> Mlty.Meta m) ms') in
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

let add_var x t ctx =
  let variables = (x, t) :: ctx.variables in
  {ctx with variables}

let add_tydef t d ctx =
  let types = (t, d) :: ctx.types in
  {ctx with types}

let add_operation op opty ctx =
  let operations = OperationMap.add op opty ctx.operations in
  {ctx with operations}

let remove_known ~known s =
  Mlty.MetaSet.fold Mlty.MetaSet.remove known s

let add_let known s ctx (x, gen, t) =
  let t = Substitution.apply s t in
  let s = match gen with
    | Ungeneralizable -> Mlty.ungeneralized_schema t
    | Generalizable ->
      let gen = Mlty.occuring t in
      let gen = remove_known ~known gen in
      let gen = Mlty.MetaSet.elements gen in
      gen, t
  in
  let variables = (x, s) :: ctx.variables in
  {ctx with variables}


let add_lets xts known s ctx =
  List.fold_left (add_let known s) ctx xts

let op_cases op ~output ctx =
  let (args, opout) = OperationMap.find op ctx.operations in
  let continuation = Some (opout, output) in
  args, {ctx with continuation}

let unfold ctx x ts =
  let _, def = List.nth (List.rev ctx.types) x in
  match def with
    | Mlty.Sum _ -> None
    | Mlty.Alias (ms, t) ->
      let s = Substitution.from_lists ms ts in
      Some (Substitution.apply s t)

let gather_known {types = _; variables; operations = _; continuation} =
  let known =
    List.fold_left
      (fun known (_, s) -> Mlty.MetaSet.union known (Mlty.occuring_schema s))
      Mlty.MetaSet.empty
      variables
  in
  let known = match continuation with
    | Some (t1, t2) ->
       Mlty.MetaSet.union known (Mlty.MetaSet.union (Mlty.occuring t1) (Mlty.occuring t2))
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

