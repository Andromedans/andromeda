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
  constants : (Name.ident * Tt.constsig) list;
  atoms : (Name.atom * Tt.ty) list;
  bound : (Name.ident * Value.value) list;
  beta : (string list list * Pattern.beta_hint list) HintMap.t;
  eta : (string list list * Pattern.eta_hint list) HintMap.t;
  (* general hints might not have a key *)
  general : (string list list * Pattern.general_hint list) GeneralMap.t *
            (string list list * Pattern.general_hint list);
  inhabit : (string list list * Pattern.inhabit_hint list) HintMap.t;
  files : string list;
}

(** The empty context *)
let empty = {
  constants = [];
  atoms = [];
  bound = [] ;
  beta = HintMap.empty ;
  eta = HintMap.empty ;
  general = GeneralMap.empty, ([], []) ;
  inhabit = HintMap.empty ;
  files = [] ;
}

let find k hs = try HintMap.find k hs with Not_found -> [], []
let find3 k hs = try GeneralMap.find k hs with Not_found -> [], []

let eta_hints key {eta=hints} = snd @@ find key hints

let beta_hints key {beta=hints} = snd @@ find key hints

let general_hints key {general=(keys,nokeys)} =
  let keyed = match key with Some key -> snd @@ find3 key keys | None -> [] in
  keyed @ snd nokeys

let inhabit_hints key {inhabit=hints} = snd @@ find key hints

let bound_names {bound=lst} = List.map fst lst

let constants {constants=lst} =
  List.map (fun (x, (yts, _)) -> (x, List.length yts)) lst

let used_names ctx =
  List.map fst ctx.bound @ List.map fst ctx.constants

let lookup_constant x {constants=lst} =
  let rec lookup = function
    | [] -> None
    | (y,v) :: lst ->
       if Name.eq_ident x y then Some v else lookup lst
  in
    lookup lst

let lookup_bound k {bound=lst} =
  try
    snd (List.nth lst k)
  with
  | Failure _ -> Error.impossible "invalid de Bruijn index %d" k

let is_bound x ctx =
  match lookup_constant x ctx with
  | None -> false
  | Some _ -> true

let add_constant x ytsu ctx =
  if is_bound x ctx
  then Error.runtime "%t already exists" (Name.print_ident x)
  else { ctx with constants = (x, ytsu) :: ctx.constants }

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
        (fun (db, ((nokey_tags, nokey_hints) as nokeys)) (xs, (key, h)) ->
           match key with
           | Some key ->
             let tags, hints = find3 key db in
             GeneralMap.add key (xs :: tags, h :: hints) db, nokeys
           | None -> db, (xs :: nokey_tags, h :: nokey_hints))
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

let unhint untags ctx =
  let pred = List.exists (fun x -> List.mem x untags) in
  let rec fold xs' hs' tags hints =
    match tags, hints with
    | [], [] -> List.rev xs', List.rev hs'
    | xs::tags, h::hints ->
      let xs', hs' =
        if pred xs
        then xs', hs'
        else xs::xs', h::hs' in
      (fold xs' hs') tags hints
    | [], _::_ | _::_, [] ->
      Error.impossible "Number of hints different from number of tags"

  in let f (tags, hints) = fold [] [] tags hints in
  { ctx with
    beta = HintMap.map f ctx.beta ;
    eta = HintMap.map f ctx.eta ;
    general =
      begin
        let nokeys = List.combine (fst @@ snd ctx.general) (snd @@ snd ctx.general) in
        let nokeys = List.split @@ List.filter (fun (xs, h) -> pred xs) nokeys in
        GeneralMap.map f (fst ctx.general), nokeys
      end ;
    inhabit = HintMap.map f ctx.inhabit ;
  }

let add_bound x v ctx =
  { ctx with bound = (x, v) :: ctx.bound }

(** generate a fresh atom of type [t] and bind it to [x]
    NB: This is an effectful computation. *)
let add_fresh ~loc ctx x t =
  let y = Name.fresh x in
  let yt = Value.Judge (Tt.mk_atom ~loc y, t) in
  let ctx = add_bound x yt ctx in
  let ctx = {ctx with atoms = (y, t) :: ctx.atoms} in
  y, ctx

let add_file f ctx =
  { ctx with files = (Filename.basename f) :: ctx.files }

let included f { files } = List.mem (Filename.basename f) files

let print ctx ppf =
  let forbidden_names = used_names ctx in
  Print.print ppf "---CONTEXT---@." ;
  List.iter
    (fun (x, t) ->
     Print.print ppf "@[<hov 4>Parameter %t@;<1 -2>%t@]@\n" (Name.print_ident x)
       (Tt.print_constsig forbidden_names t))
    (List.rev ctx.constants) ;
  Print.print ppf "-----END-----@."
