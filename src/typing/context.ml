open Amltype

type constrain =
  | AppConstraint of Location.t * ty * ty * ty

type generalizable =
  | Generalizable
  | Ungeneralizable

let rec generalizable c = match c.Location.thing with
(* yes *)
  | Syntax.Bound _ | Syntax.Function _ | Syntax.Handler _ -> Generalizable
  | Syntax.Constructor (_, cs) | Syntax.Tuple cs ->
    if List.for_all (fun c -> generalizable c = Generalizable) cs
    then Generalizable
    else Ungeneralizable

(* who knows *)
  | Syntax.Let _ | Syntax.LetRec _ | Syntax.Sequence _ -> Ungeneralizable

(* no *)
  | _ -> Ungeneralizable

module OperationMap = Name.IdentMap

type t = {
  types : (Name.ident * ty_def) list; (* types are accessed by De Bruijn level, the name is for printing only. *)
  variables : (Name.ident * ty_schema) list; (* variables are accessed by De Bruijn index, the name is for printing only. *)
  operations : (ty list * ty) OperationMap.t;
  continuation : (ty * ty) option;
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
    | (_, Alias _) :: types -> fold types
    | (x, Sum (ms, constructors)) :: types ->
      let rec search = function
        | [] -> fold types
        | (c', ts) :: _ when Name.eq_ident c c' ->
          let s, ms' = Substitution.freshen_metas ms in
          let ts = List.map (Substitution.apply s) ts
          and out = App (x, List.length types, List.map (fun m -> Meta m) ms') in
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
  MetaSet.fold MetaSet.remove known s

let add_let known s ctx (x, gen, t) =
  let t = Substitution.apply s t in
  let s = match gen with
    | Ungeneralizable -> ungeneralized_schema t
    | Generalizable ->
      let gen = occuring t in
      let gen = remove_known ~known gen in
      let gen = MetaSet.elements gen in
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
    | Sum _ -> None
    | Alias (ms, t) ->
      let s = Substitution.from_lists ms ts in
      Some (Substitution.apply s t)

let gather_known {types = _; variables; operations = _; continuation} =
  let known = List.fold_left (fun known (_, s) -> MetaSet.union known (occuring_schema s)) MetaSet.empty variables in
  let known = match continuation with
    | Some (t1, t2) -> MetaSet.union known (MetaSet.union (occuring t1) (occuring t2))
    | None -> known
  in
  known

