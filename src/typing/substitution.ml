module MetaMap = Map.Make(struct
  type t = Mlty.meta
  let compare = compare
  end)

type t = Mlty.ty MetaMap.t

let lookup m s =
  try Some (MetaMap.find m s)
  with Not_found -> None

let apply (s : t) t =
  if MetaMap.is_empty s
  then t
  else begin
      let rec app = function

        | Mlty.Jdg | Mlty.String | Mlty.Param _ as t -> t

        | Mlty.Meta m as orig ->
           begin match lookup m s with
                 | Some t -> t
                 | None -> orig
           end

        | Mlty.Prod ts ->
           let ts = List.map app ts in
           Mlty.Prod ts

        | Mlty.Arrow (t1, t2) ->
           let t1 = app t1
           and t2 = app t2 in
           Mlty.Arrow (t1, t2)

        | Mlty.Handler (t1, t2) ->
           let t1 = app t1
           and t2 = app t2 in
           Mlty.Handler (t1, t2)

        | Mlty.App (x, k, ts) ->
           let ts = List.map app ts in
           Mlty.App (x, k, ts)

        | Mlty.Ref t ->
           let t = app t in
           Mlty.Ref t
      in
      app t
    end

let empty : t = MetaMap.empty

let from_lists ms ts =
  List.fold_left2 (fun s m t ->
      MetaMap.add m t s)
    empty ms ts

let add m t s =
  let t = apply s t in
  if Mlty.occurs m t
  then
    None
  else
    let s = MetaMap.map (apply (MetaMap.singleton m t)) s in
    Some (MetaMap.add m t s)


let gather_known s =
  MetaMap.fold (fun m _t known ->
      Mlty.MetaSet.add m known)
    s Mlty.MetaSet.empty

