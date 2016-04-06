open Amltype

module MetaMap = Map.Make(struct
  type t = meta
  let compare = compare
  end)

type t = ty MetaMap.t

let lookup m s =
  try Some (MetaMap.find m s)
  with Not_found -> None

let apply (s : t) t =
  if MetaMap.is_empty s then t
  else
  let rec aux = function
    | Jdg | String as t -> t
    | Meta m as orig ->
      begin match lookup m s with
        | Some t -> t
        | None -> orig
      end
    | Tuple ts ->
      let ts = List.map aux ts in
      Tuple ts
    | Arrow (t1, t2) ->
      let t1 = aux t1
      and t2 = aux t2 in
      Arrow (t1, t2)
    | Handler (t1, t2) ->
      let t1 = aux t1
      and t2 = aux t2 in
      Handler (t1, t2)
    | App (x, k, ts) ->
      let ts = List.map aux ts in
      App (x, k, ts)
    | Ref t ->
      let t = aux t in
      Ref t
  in
  aux t

let empty : t = MetaMap.empty

let freshen_metas ms =
  let s, ms' = List.fold_left (fun (s, ms') m ->
      let m' = fresh_meta () in
      MetaMap.add m (Meta m') s, m' :: ms')
    (empty, []) ms
  in
  s, List.rev ms'

let from_lists ms ts =
  List.fold_left2 (fun s m t ->
      MetaMap.add m t s)
    empty ms ts

let add m t s =
  let t = apply s t in
  if occurs m t
  then
    None
  else
    let s = MetaMap.map (apply (MetaMap.singleton m t)) s in
    Some (MetaMap.add m t s)

let gather_known s =
  MetaMap.fold (fun m _t known ->
      MetaSet.add m known)
    s MetaSet.empty

