module AtomSet = Name.AtomSet
module AtomMap = Name.AtomMap


(* A context is a map which assigns to an atom its type and the dependencies and dependants respectively.
   We can think of it as a directed graph whose vertices are the atoms, labelled by
   the type, and the sets of atoms are the two directions of edges. *)

type node =
  { ty : Tt.ty; (* type of x *)
    needed_by : AtomSet.t } (* atoms which depend on x *)

type t = node AtomMap.t

type error =
  | AbstractDependency of Name.atom * Name.atom list
  | AbstractInvalidType of Name.atom * Tt.ty * Tt.ty
  | InvalidJoin of t * t * Name.atom
  | SubstitutionDependency of Name.atom * Tt.term * Name.atom
  | SubstitutionInvalidType of Name.atom * Tt.ty * Tt.ty

exception Error of error Location.located

let error ~loc err = raise (Error (Location.locate err loc))

let empty = AtomMap.empty

let is_empty = AtomMap.is_empty

let print_dependencies ~printer s v ppf =
  if not !Config.print_dependencies || AtomSet.is_empty v
  then Format.fprintf ppf ""
  else Format.fprintf ppf "@ %s[%t]" s
                      (Print.sequence (Name.print_atom ~printer) "," (AtomSet.elements v))

let print_entry ~penv ppf x {ty; needed_by;} =
  Format.fprintf ppf "%t : @[<hov>%t@ @[<h>%t@]@]@ "
    (Name.print_atom ~printer:(penv.Tt.atoms) x)
    (Tt.print_ty ~penv ty)
    (print_dependencies ~printer:(penv.Tt.atoms) "needed_by" needed_by)

let print ~penv ctx ppf =
  Format.pp_open_vbox ppf 0 ;
  AtomMap.iter (print_entry ~penv ppf) ctx ;
  Format.pp_close_box ppf ()

let print_error ~penv err ppf =
  match err with

  | AbstractDependency (x, needed_by_l) ->
     Format.fprintf ppf "cannot abstract@ %t@ because@ %t@ depend%s on it"
          (Name.print_atom ~printer:penv.Tt.atoms x)
          (Print.sequence (Name.print_atom ~printer:penv.Tt.atoms) "," needed_by_l)
          (match needed_by_l with [_] -> "s" | _ -> "")

  | AbstractInvalidType (x, t1, t2) ->
     Format.fprintf ppf "cannot abstract@ %t@ with type@ %t@ because it must have type@ %t"
        (Name.print_atom ~printer:penv.Tt.atoms x)
        (Tt.print_ty ~penv t1)
        (Tt.print_ty ~penv t2)

  | InvalidJoin (ctx1, ctx2, x) ->
     Format.fprintf ppf "cannot join contexts@ %t and@ %t at %t"
                    (print ~penv ctx1)
                    (print ~penv ctx2)
                    (Name.print_atom ~printer:penv.Tt.atoms x)

  | SubstitutionDependency (x, e, y) ->
     Format.fprintf ppf "cannot substitute@ %t@ with@ %t,@ dependency cycle at@ %t"
                (Name.print_atom ~printer:penv.Tt.atoms x)
                (Tt.print_term ~penv e)
                (Name.print_atom ~printer:penv.Tt.atoms y)

  | SubstitutionInvalidType (x, x_ty, t) ->
     Format.fprintf ppf "cannot substitute term of type %t for %t of type %t"
                    (Tt.print_ty ~penv t)
                    (Name.print_atom ~printer:penv.Tt.atoms x)
                    (Tt.print_ty ~penv x_ty)


let lookup x (ctx : t) =
  try Some (AtomMap.find x ctx)
  with Not_found -> None

let lookup_ty x ctx =
  match lookup x ctx with None -> None | Some {ty;_} -> Some ty

let is_subset ctx yts =
  AtomMap.fold
    (fun x node ok ->
     ok && 
     (try
         let t' = List.assoc x yts in
         Tt.alpha_equal_ty t' node.ty
      with Not_found -> false))
    ctx true

let recursive_assumptions ctx aset =
  let rec fold visited = function
    | [] -> visited
    | x::rem ->
      if AtomSet.mem x visited
      then fold visited rem
      else
        let visited = AtomSet.add x visited in
        let {ty;_} = AtomMap.find x ctx in
        let aset = Tt.assumptions_ty ty in
        let rem = List.rev_append (AtomSet.elements aset) rem in
        fold visited rem
  in
  fold AtomSet.empty (AtomSet.elements aset)

let add_fresh ctx x ty =
  let y = Name.fresh x in
  let aset = Tt.assumptions_ty ty in
  let needs = recursive_assumptions ctx aset in
  let ctx = AtomMap.mapi (fun z node ->
                          if AtomSet.mem z needs
                          then {node with needed_by = AtomSet.add y node.needed_by}
                          else node)
                         ctx
  in
  y, AtomMap.add y {ty;needed_by = AtomSet.empty;} ctx

let restrict ctx aset =
  let domain = recursive_assumptions ctx aset in
  let res = AtomMap.fold (fun x node res ->
      if AtomSet.mem x domain
      then
        AtomMap.add x {node with needed_by = AtomSet.inter node.needed_by domain} res
      else res)
    ctx empty
  in
  res

let abstract ~loc (ctx : t) x ty =
  match lookup x ctx with
  | None ->
     ctx
  | Some node ->
    if Tt.alpha_equal_ty node.ty ty
    then
      if AtomSet.is_empty node.needed_by
      then
        let ctx = AtomMap.remove x ctx in
        let ctx = AtomMap.map (fun node -> {node with needed_by = AtomSet.remove x node.needed_by}) ctx in
        ctx
      else
        let needed_by_l = AtomSet.elements node.needed_by in
        error ~loc (AbstractDependency (x, needed_by_l))
    else
      error ~loc (AbstractInvalidType (x, ty, node.ty))

let join ~loc ctx1 ctx2 =
  AtomMap.fold (fun x node res ->
      match lookup x res with
        | Some node' ->
          if Tt.alpha_equal_ty node.ty node'.ty
          then
            (* for every node which needs x and is only in ctx2, we need to add it as a dependent. *)
            let extra = AtomSet.fold (fun y extra ->
                if AtomMap.mem y ctx1
                then extra
                else AtomSet.add y extra)
              node.needed_by AtomSet.empty
            in
            if AtomSet.is_empty extra
            then res
            else AtomMap.add x {node' with needed_by = AtomSet.union node'.needed_by extra} res
          else
            error ~loc (InvalidJoin (ctx1, ctx2, x))
        | None ->
          (* dependencies are handled above *)
          AtomMap.add x node res)
    ctx2 ctx1

let subst_ty ty x e =
  let ty = Tt.abstract_ty [x] ty in
  let ty = Tt.instantiate_ty [e] ty in
    ty

(* substitute x by e in ctx *)
let substitute ~loc x (ctx,e,t) =
  match lookup x ctx with
    | Some xnode ->
      if Tt.alpha_equal_ty xnode.ty t
      then
        (* NB: rec_assumptions(t) <= rec_assumptions(e) *)
        let deps = recursive_assumptions ctx (Tt.assumptions_term e) in
        let ctx = AtomSet.fold (fun y ctx ->
            let ynode = AtomMap.find y ctx in
            if AtomSet.mem y deps
            then
              error ~loc (SubstitutionDependency (x, e, y))
            else
              let ty = subst_ty ynode.ty x e in
              AtomMap.add y {ynode with ty} ctx)
          xnode.needed_by ctx
        in
        let ctx = AtomSet.fold (fun z ctx ->
            let znode = AtomMap.find z ctx in
            let needed_by = AtomSet.union znode.needed_by xnode.needed_by in
            AtomMap.add z {znode with needed_by} ctx)
          deps ctx
        in
        if AtomSet.mem x deps
        then ctx
        else
          (* we can remove x *)
          let ctx = AtomMap.remove x ctx in
          let ctx = AtomMap.map (fun node -> {node with needed_by = AtomSet.remove x node.needed_by}) ctx in
          ctx
      else
        error ~loc (SubstitutionInvalidType (x, xnode.ty, t))
    | None -> ctx


let elements ctx =
  let rec process x ((handled, _) as handled_ys) =
    if AtomSet.mem x handled
    then handled_ys
    else
      let {needed_by;ty} = AtomMap.find x ctx in
      let (handled, xts) = AtomSet.fold process needed_by handled_ys  in
      (AtomSet.add x handled, (x,ty) :: xts)
  in
  let _, xts = AtomMap.fold (fun x _ -> process x) ctx (AtomSet.empty, []) in
  xts

