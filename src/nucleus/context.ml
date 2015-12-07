
module AtomMap = Map.Make (struct
                      type t = Name.atom
                      let compare = Name.compare_atom
                    end)

module AtomSet = Name.AtomSet


(* A context is a map which assigns to an atom its type and the dependencies and dependants respectively.
   We can think of it as a directed graph whose vertices are the atoms, labelled by
   the type, and the sets of atoms are the two directions of edges. *)

type node =
  { ty : Tt.ty; (* type of x *)
    needed_by : AtomSet.t } (* atoms which depend on x *)

type t = node AtomMap.t

let empty = AtomMap.empty

let print_dependencies s v ppf =
  if not !Config.print_dependencies || AtomSet.is_empty v
  then Format.fprintf ppf ""
  else Format.fprintf ppf "@ %s[%t]" s
                      (Print.sequence Name.print_atom "," (AtomSet.elements v))

let print_entry ppf x {ty; needed_by;} =
  Format.fprintf ppf "%t : @[<hov>%t@ @[<h>%t@]@]@ "
    (Name.print_atom x)
    (Tt.print_ty [] ty)
    (print_dependencies "needed_by" needed_by)

let print ctx ppf =
  Format.pp_open_vbox ppf 0 ;
  AtomMap.iter (print_entry ppf) ctx ;
  Format.pp_close_box ppf ()

let lookup x (ctx : t) =
  try Some (AtomMap.find x ctx)
  with Not_found -> None

let lookup_ty x ctx =
  match lookup x ctx with None -> None | Some {ty;_} -> Some ty


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

let add ctx x ty =
  match lookup_ty x ctx with
    | Some ty' ->
      if Tt.alpha_equal_ty ty ty'
      then
        Some ctx
      else
        None
    | None ->
      let aset = Tt.assumptions_ty ty in
      let needs = recursive_assumptions ctx aset in
      let ctx = AtomMap.mapi (fun y node ->
          if AtomSet.mem y needs
          then {node with needed_by = AtomSet.add x node.needed_by}
          else node)
        ctx
      in
      let ctx = AtomMap.add x {ty;needed_by = AtomSet.empty;} ctx in
      Some ctx

let add_fresh ctx x ty =
  let y = Name.fresh x in
  match add ctx y ty with
    | Some ctx -> y,ctx
    | None ->
      let Tt.Ty {Tt.loc=loc;_} = ty in
      Error.impossible ~loc "Encountered freshly generated atom %t" (Name.print_atom y)

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


type ('a,'b) err =
  | OK of 'a
  | Err of 'b

let abstract ~loc (ctx : t) x ty =
  match lookup x ctx with
  | None ->
     OK ctx
  | Some node ->
    if Tt.alpha_equal_ty node.ty ty
    then
      if AtomSet.is_empty node.needed_by
      then
        let ctx = AtomMap.remove x ctx in
        let ctx = AtomMap.map (fun node -> {node with needed_by = AtomSet.remove x node.needed_by}) ctx in
        OK ctx
      else
        Err node.needed_by
    else
      Error.runtime ~loc "cannot abstract %t with type %t because it must have type %t."
        (Name.print_atom x)
        (Tt.print_ty [] ty)
        (Tt.print_ty [] node.ty)
       

let join ctx1 ctx2 =
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
          else Error.runtime ~loc:Location.unknown "cannot join contexts: types %t and %t of %t are incompatible."
              (Tt.print_ty [] node'.ty)
              (Tt.print_ty [] node.ty)
              (Name.print_atom x)
        | None ->
          (* dependencies are handled above *)
          AtomMap.add x node res)
    ctx2 ctx1

let subst_ty ty x e =
  let ty = Tt.abstract_ty [x] ty in
  let ty = Tt.instantiate_ty [e] ty in
    ty

(* substitute x by e in ctx, assuming both have type t *)
let substitute ~loc x (ctx,e,t) =
  match lookup x ctx with
    | Some xnode ->
      (* NB: rec_assumptions(t) <= rec_assumptions(e) *)
      let deps = recursive_assumptions ctx (Tt.assumptions_term e) in
      let ctx = AtomSet.fold (fun y ctx ->
          let ynode = AtomMap.find y ctx in
          if AtomSet.mem y deps
          then Error.runtime ~loc "cannot substitute %t with %t: dependency cycle at %t."
              (Name.print_atom x)
              (Tt.print_term [] e)
              (Name.print_atom y)
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
    | None -> ctx

