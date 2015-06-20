(** Typing context and runtime environment *)

module HintMap = Map.Make(struct
    type t = Pattern.hint_key
    let compare = Pervasives.compare
  end)
module GeneralMap = Map.Make(struct
    type t = Pattern.hint_key * Pattern.hint_key * Pattern.hint_key
    let compare = Pervasives.compare
  end)

(** A context holds free variables with their types and an
    environment of runtime bindings. *)
type t = {
  free : (Name.t * Tt.ty) list;
  primitive : (Name.t * Tt.primsig) list;
  bound : (Name.t * Value.value) list;
  beta : (string list list * Pattern.beta_hint list) HintMap.t;
  eta : (string list list * Pattern.eta_hint list) HintMap.t;
  general : (string list list * Pattern.general_hint list) GeneralMap.t;
  inhabit : (string list list * Pattern.inhabit_hint list) HintMap.t;
  files : string list;
}

(** The empty context *)
let empty = {
  free = [];
  primitive = [];
  bound = [] ;
  beta = HintMap.empty ;
  eta = HintMap.empty ;
  general = GeneralMap.empty ;
  inhabit = HintMap.empty ;
  files = [] ;
}

let find k hs = try HintMap.find k hs with Not_found -> [], []
let find3 k hs = try GeneralMap.find k hs with Not_found -> [], []

let eta_hints key {eta=hints} = snd @@ find key hints

let beta_hints key {beta=hints} = snd @@ find key hints

let general_hints key {general=hints} = snd @@ find3 key hints

let inhabit_hints key {inhabit=hints} = snd @@ find key hints

let bound_names {bound=lst} = List.map fst lst

let primitives {primitive=lst} =
  List.map (fun (x, (yts, _)) -> (x, List.length yts)) lst

let used_names ctx =
  List.map fst ctx.free @ List.map fst ctx.bound @ List.map fst ctx.primitive

let lookup_free x {free=lst} =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq x y then Some v else lookup lst
  in
    lookup lst

let lookup_primitive x {primitive=lst} =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq x y then Some v else lookup lst
  in
    lookup lst

let lookup_bound k {bound=lst} =
  try
    snd (List.nth lst k)
  with
  | Failure _ -> Error.impossible "invalid de Bruijn index %d" k

let is_bound x ctx =
  match lookup_free x ctx with
  | None ->
    begin match lookup_primitive x ctx with
      | None -> false
      | Some _ -> true
    end
  | Some _ -> true

let add_free x t ctx =
  if is_bound x ctx
  then Error.runtime "%t already exists" (Name.print x)
  else { ctx with free = (x,t) :: ctx.free }

let add_primitive x ytsu ctx =
  if is_bound x ctx
  then Error.runtime "%t already exists" (Name.print x)
  else { ctx with primitive = (x, ytsu) :: ctx.primitive }

let add_betas xshs ctx =
  { ctx with
    beta =
      List.fold_left
        (fun db (xs, (key, h)) ->
           let tags, hints = find key db in
           HintMap.add key (xs :: tags, h :: hints) db)
        ctx.beta xshs
  }

let add_etas xshs ctx =
  { ctx with
    eta =
      List.fold_left
        (fun db (xs, (key, h)) ->
           let tags, hints = find key db in
           HintMap.add key (xs :: tags, h :: hints) db)
        ctx.eta xshs
  }

let add_generals xshs ctx =
  { ctx with
    general =
      List.fold_left
        (fun db (xs, (key, h)) ->
           let tags, hints = find3 key db in
           GeneralMap.add key (xs :: tags, h :: hints) db)
        ctx.general xshs
  }

let add_inhabits xshs ctx =
  { ctx with
    inhabit =
      List.fold_left
        (fun db (xs, (key, h)) ->
           let tags, hints = find key db in
           HintMap.add key (xs :: tags, h :: hints) db)
        ctx.inhabit xshs
  }

let add_fresh x t ctx =
  let y = Name.fresh x
  in y, { ctx with free = (y,t) :: ctx.free }

let add_bound x v ctx =
  { ctx with bound = (x, v) :: ctx.bound }

let add_file f ctx =
  { ctx with files = (Filename.basename f) :: ctx.files }

let included f { files } = List.mem (Filename.basename f) files

let print ctx ppf =
  let forbidden_names = used_names ctx in
  Print.print ppf "---CONTEXT---@." ;
  List.iter
    (fun (x, t) ->
     Print.print ppf "@[<hov 4>Parameter %t@;<1 -2>%t@]@\n" (Name.print x)
       (Tt.print_primsig forbidden_names t))
    (List.rev ctx.primitive) ;
  Print.print ppf "-----END-----@."
