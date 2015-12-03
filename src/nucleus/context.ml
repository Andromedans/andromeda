type renaming = (Name.atom * Name.atom) list

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
    needs : AtomSet.t; (* atoms which x depends on *)
    needed_by : AtomSet.t } (* atoms which depend on x *)

type t = node AtomMap.t

let empty = AtomMap.empty

let print_dependencies s v ppf =
  if not !Config.print_dependencies || AtomSet.is_empty v
  then Format.fprintf ppf ""
  else Format.fprintf ppf "@ %s[%t]" s
                      (Print.sequence Name.print_atom "," (AtomSet.elements v))

let print_entry ppf x {ty; needs; needed_by;} =
  Format.fprintf ppf "%t : @[<hov>%t@ @[<h>%t@]@[<h>%t@]@]@ "
    (Name.print_atom x)
    (Tt.print_ty [] ty)
    (print_dependencies "needs" needs)
    (print_dependencies "needed_by" needed_by)

let print ctx ppf =
  Format.pp_open_vbox ppf 0 ;
  AtomMap.iter (print_entry ppf) ctx ;
  Format.pp_close_box ppf ()

let as_set (ctx : t) = AtomMap.fold (fun x _ s -> AtomSet.add x s) ctx AtomSet.empty

let lookup x (ctx : t) =
  try Some (AtomMap.find x ctx)
  with Not_found -> None

let lookup_ty x ctx =
  match lookup x ctx with None -> None | Some {ty;_} -> Some ty

let cone ctx x (ty : Tt.ty) =
  let y = Name.fresh x in
  let ctx = AtomMap.map (fun node -> {node with needed_by = AtomSet.add y node.needed_by}) ctx in
  let ctx = AtomMap.add y {ty; needs=as_set ctx; needed_by=AtomSet.empty;} ctx in
  y, ctx


let context_at ctx x =
  let {needs;_} = AtomMap.find x ctx in
  let ctx' = AtomSet.fold (fun y ctx' ->
      let node = AtomMap.find y ctx in
        AtomMap.add y {node with needed_by = AtomSet.inter node.needed_by needs} ctx')
    needs empty in
  ctx'

let abstract1 ~loc (ctx : t) x =
  match lookup x ctx with
  | None ->
     ctx
  | Some node ->
     if AtomSet.is_empty node.needed_by
     then
       let ctx = AtomMap.remove x ctx in
       let ctx = AtomMap.map (fun node -> {node with needed_by = AtomSet.remove x node.needed_by}) ctx in
       ctx
     else
       let needed_by_l = AtomSet.elements node.needed_by in
       Error.runtime
         ~loc "cannot abstract %t because %t depend%s on it.\nContext:@ %t"
                     (Name.print_atom x)
                     (Print.sequence (Name.print_atom) "," needed_by_l)
                     (match needed_by_l with [_] -> "s" | _ -> "")
                     (print ctx)

let abstract ~loc ctx xs = List.fold_left (abstract1 ~loc) ctx xs

let rename (ctx : t) s =
  let a_s, b_s = List.split s in
  AtomMap.fold
    (fun a node ctx ->
      let b = try List.assoc a s with Not_found -> a
      and ty = Tt.abstract_ty a_s node.ty |> Tt.unabstract_ty b_s
      and needs =
        AtomSet.fold
          (fun x needs -> AtomSet.add (try List.assoc x s with Not_found -> x) needs)
          node.needs AtomSet.empty
      and needed_by =
        AtomSet.fold
          (fun x needed_by -> AtomSet.add (try List.assoc x s with Not_found -> x) needed_by)
          node.needed_by AtomSet.empty
      in
        AtomMap.add b {ty; needs; needed_by} ctx)
    ctx
    empty

let refresh ctx =
  let a_s = AtomMap.bindings ctx |> List.map fst in
  let b_s = List.map Name.refresh_atom a_s in
  (rename ctx (List.combine a_s b_s),
   (List.combine b_s a_s))


(** Sort the entries of [ctx] into a list so that all dependencies
    point forward in the list. *)
let topological_sort ctx =
  let rec process x ((handled, _) as handled_ys) =
    if AtomSet.mem x handled
    then handled_ys
    else
      let {needed_by;_} = AtomMap.find x ctx in
      let (handled, ys) = AtomSet.fold process needed_by handled_ys  in
      (AtomSet.add x handled, x :: ys)
  in
  let _, ys = AtomMap.fold (fun x _ -> process x) ctx (AtomSet.empty, []) in
  ys


let mk_eq (Tt.Ty ty) (Tt.Ty ty') = Tt.mk_eq_ty ~loc:Location.unknown Tt.typ ty ty'

(** Extend the context [ctx] such that ctx |- x : ty while keeping track of specific dependency information. *)
let extend ctx xneeds x ty =
  match lookup x ctx with
  | None ->
    let ctx = AtomMap.mapi (fun y node ->
        if AtomSet.mem y xneeds
        then {node with needed_by = AtomSet.add x node.needed_by}
        else node)
      ctx in
    let ctx = AtomMap.add x {ty; needs=xneeds; needed_by=AtomSet.empty;} ctx in
    ctx, AtomSet.add x xneeds
  | Some xnode ->
    if Tt.alpha_equal_ty ty xnode.ty
    then ctx, AtomSet.add x xnode.needs
    else let e = Name.fresh (Name.make "__eq") in
      let xneeds = AtomSet.union xneeds xnode.needs in
      let ctx = AtomMap.mapi (fun y node ->
          if AtomSet.mem y xneeds
          then {node with needed_by = AtomSet.add e node.needed_by}
          else node)
        ctx in
      let ctx = AtomMap.add e
        {ty=mk_eq ty xnode.ty; needs=xneeds; needed_by=AtomSet.empty;}
        ctx in
      let xneeds = AtomSet.add e xneeds in
        ctx, AtomSet.add x xneeds


(** Make a context stronger than ctx1 and ctx2 while keeping track of dependencies. *)
let join' ctx1 ctx2 =
  let rec joinA ctx f = function
    | [] -> ctx, f
    | x::l -> let {ty; needs;_} = AtomMap.find x ctx2 in (* ctx2_needs |- ty : Type *)
      let needs = AtomSet.fold (* ctx_needs |- ty : Type *)
        (fun y needs -> AtomSet.union needs (AtomMap.find y f))
        needs
        AtomSet.empty in
      let ctx, needs = extend ctx needs x ty in (* ctx_needs |- x : ty *)
      let f = AtomMap.add x needs f in
        joinA ctx f l
    in joinA ctx1 empty (topological_sort ctx2)

let join ctx1 ctx2 = let ctx,_ = join' ctx1 ctx2 in ctx


(** Substitute a variable by a judgment in a context. *)

let split_around ctx x xrevs =
  let sorted = topological_sort ctx in
  let rec split needs revs = function
    | [] -> needs, List.rev revs
    | y::l -> if Name.eq_atom x y
      then split needs revs l
      else begin if AtomSet.mem y xrevs
        then split needs (y::revs) l
        else let ynode = AtomMap.find y ctx in
          let yrevs = AtomSet.fold
            (fun r yrevs -> AtomSet.remove r yrevs)
            xrevs
            (AtomSet.remove x ynode.needed_by) in
          split (AtomMap.add y {ynode with needed_by = yrevs} needs) revs l
      end
    in split empty [] sorted

let subst_ty ty x e =
  let ty = Tt.abstract_ty [x] ty in
  let ty = Tt.instantiate_ty [e] ty in
    ty



(**
ctx1 |- x : A
ctx2 |- e : A
*)

let substitute ctx1 x (ctx2,e,ty_e) = match lookup x ctx1 with
  | None -> ctx1 (* note that the spec doesn't require us to add ctx2 when x notin ctx1 *)
  | Some xnode ->
    let ctxl1, ctxr1 = split_around ctx1 x xnode.needed_by in
    let ctx', f = join' ctx2 ctxl1 in
    let eneeds = as_set ctx2 in

    (* Now ctx'_{eneeds} |- ty == ty_e and |- e : ty_e thus |- e : ty *)
    let rec substA ctx' f = function (* for each processed y from ctx1, ctx'_{f(y)} |- y : subst (ctx1(y)) x e *)
      | [] -> ctx'
      | y::l -> let ynode = AtomMap.find y ctx1 in
        let yneeds = AtomSet.fold
          (fun z yneeds -> if Name.eq_atom x z
            then yneeds
            else AtomSet.union yneeds (AtomMap.find z f))
          ynode.needs
          eneeds in
        (* yneeds such that preconditions for the next line *)
        let ctx', yneeds = extend ctx' yneeds y (subst_ty ynode.ty x e) in
        let f = AtomMap.add y yneeds f in
          substA ctx' f l
      in substA ctx' f ctxr1

