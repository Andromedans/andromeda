(** The typing context *)

(* Type-checking assigns identifiers to types and operations, as these can be
   statically determined. It cannot do so for TT constructors and ML values,
   because they are computed at runtime. *)

type ml_module = {
  ml_types : (Ident.t * Mlty.ty_def) list;
  ml_operations : (Ident.t * (Mlty.ty list * Mlty.ty)) list;
  tt_constructors : (Ident.t * Mlty.tt_constructor) list ;
  ml_values : (Name.t * Mlty.ty_schema) list;
}

type t = {
    ml_modules : (Ident.t * ml_module) list;
    current_ml_types : (Ident.t * Mlty.ty_def) list ;
    current_ml_operations : (Ident.t * (Mlty.ty list * Mlty.ty)) list ;
    current_tt_constructors : (Ident.t * Mlty.tt_constructor) list ;
    current_ml_values : (Name.t * Mlty.ty_schema) list; (** accessed by index *)
    ml_yield : (Mlty.ty * Mlty.ty) option
  }

let empty = {
    ml_modules = [];
    current_ml_types = [];
    current_ml_operations = [];
    current_tt_constructors = [];
    current_ml_values = [];
    ml_yield = None
  }

let lookup_bound (Path.Index (_, k)) {current_ml_values;_} =
  let _, (ps, t) = List.nth current_ml_values k in
  let pus = List.map (fun p -> (p, Mlty.fresh_type ())) ps in
  Mlty.instantiate pus t

let lookup_ml_module (Path.Level (_, l)) {ml_modules;_} =
  List.nth ml_modules l

let lookup_ml_value pth ctx =
  match pth with

  | Path.Direct _ ->
     (* It should never happen that a value in the current context is
        looked up by level. They are looked up by index. *)
     assert false

  | Path.Module (mdl_lvl, Path.Level (_, l)) ->
     let _, mdl = lookup_ml_module mdl_lvl ctx in
     let _, (ps, t) = List.nth mdl.ml_values l in
     let pus = List.map (fun p -> (p, Mlty.fresh_type ())) ps in
     let t = Mlty.instantiate pus t in
     Mlty.shift mdl_lvl t

let lookup_ml_operation pth ctx =
  match pth with

  | Path.Direct (Path.Level (_, l)) ->
     List.nth ctx.current_ml_operations l

  | Path.Module (mdl_lvl, Path.Level (_, l)) ->
     let _, mdl = lookup_ml_module mdl_lvl ctx in
     let oid, (ts,t) = List.nth mdl.ml_operations l in
     let ts = List.map (Mlty.shift mdl_lvl) ts
     and t = Mlty.shift mdl_lvl t in
     oid,  (ts, t)

let lookup_tt_constructor pth ctx =
  match pth with

  | Path.Direct (Path.Level (_, l)) ->
     List.nth ctx.current_tt_constructors l

  | Path.Module (mdl_lvl, Path.Level (_, l)) ->
     let _, mdl = lookup_ml_module mdl_lvl ctx in
     List.nth mdl.tt_constructors l

let lookup_ml_type_id t_pth ctx =
  match t_pth with

  | Path.Direct (Path.Level (_, l)) ->
     fst (List.nth ctx.current_ml_types l)

  | Path.Module (mdl_lvl, Path.Level (_, l)) ->
     let _, mdl = lookup_ml_module mdl_lvl ctx in
     fst (List.nth mdl.ml_types l)

let lookup_ml_type t_pth ctx =
  match t_pth with

  | Path.Direct (Path.Level (_, l)) ->
     List.nth ctx.current_ml_types l

  | Path.Module (mdl_lvl, Path.Level (_, l)) ->
     let _, mdl = lookup_ml_module mdl_lvl ctx in
     begin match List.nth mdl.ml_types l with

     | t_id, Mlty.Alias (ps, t) ->
        let t = Mlty.shift mdl_lvl t in
        t_id, Mlty.Alias (ps, t)

     | t_id, Mlty.Sum (ps, cs) ->
        let cs = List.map (fun (c, ts) -> (c, List.map (Mlty.shift mdl_lvl) ts)) cs in
        t_id, Mlty.Sum (ps, cs)
     end

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
  { ctx with current_tt_constructors  = (c,t) :: ctx.current_tt_constructors }

let add_ml_type t d ctx =
  let t = Ident.create t in
  { ctx with current_ml_types = (t, d) :: ctx.current_ml_types }

let add_ml_operation op opty ctx =
  let op = Ident.create op in
  { ctx with current_ml_operations = (op, opty) :: ctx.current_ml_operations }

let add_ml_value x s ctx =
  { ctx with current_ml_values = (x, s) :: ctx.current_ml_values }

let op_cases op ~output ctx =
  let (oid, (args, opout)) = lookup_ml_operation op ctx in
  oid, args, { ctx with ml_yield = Some (opout, output) }

let unfold ctx t_pth ts =
  match lookup_ml_type t_pth ctx with
    | _, Mlty.Sum _ -> None
    | _, Mlty.Alias (ps, t) ->
       let pus = List.combine ps ts in
       Some (Mlty.instantiate pus t)

let gather_known s {current_ml_values; ml_yield; _} =
  let subst = Substitution.apply s in
  let known =
    List.fold_left
      (fun known (_, (_, t)) -> Mlty.MetaSet.union known (Mlty.occuring (subst t)))
      Mlty.MetaSet.empty
      current_ml_values
  in
  let known = match ml_yield with
    | Some (t1, t2) ->
       Mlty.MetaSet.union known (Mlty.MetaSet.union (Mlty.occuring (subst t1)) (Mlty.occuring (subst t2)))
    | None -> known
  in
  known

let print_context {current_ml_values;_} =
  let penv = Mlty.fresh_penv () in
  List.iter
    (fun (x, sch) ->
      Format.printf
        "%t : %t@\n"
        (Name.print x)
        (Mlty.print_ty_schema ~penv sch)
    )
    current_ml_values
