module MetaMap = Map.Make(struct
  type t = Mlty.meta
  let compare = compare
  end)

type t = Mlty.ty MetaMap.t

let lookup m s =
  try Some (MetaMap.find m s)
  with Not_found -> None

let domain s =
  MetaMap.fold (fun m _ ms -> Mlty.MetaSet.add m ms) s Mlty.MetaSet.empty

let apply (s : t) t =
  if MetaMap.is_empty s
  then t
  else begin
      let rec app = function
        | Mlty.Exn
        | Mlty.Judgement
        | Mlty.Boundary
        | Mlty.Derivation
        | Mlty.String
        | Mlty.Param _ as t -> t

        | Mlty.Meta m as orig ->
           begin match lookup m s with
                 | Some t -> app t
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

        | Mlty.Apply (pth, ts) ->
           let ts = List.map app ts in
           Mlty.Apply (pth, ts)

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
    Some (MetaMap.add m t s)

let partition = MetaMap.partition
