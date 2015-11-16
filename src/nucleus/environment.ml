module HintMap = Map.Make(struct
    type t = Pattern.hint_key
    let compare = Pervasives.compare
  end)

module GeneralMap = Map.Make(struct
    type t = Pattern.general_key
    let compare = Pervasives.compare
  end)

(** An environment holds constant signatures, hints and other. *)
type t = {
  constants : (Name.ident * Tt.constsig) list;
  bound : (Name.ident * Value.value) list;
  beta : (string list list * Pattern.beta_hint list) HintMap.t;
  eta : (string list list * Pattern.eta_hint list) HintMap.t;
  general : (string list list * Pattern.general_hint list) GeneralMap.t;
  inhabit : (string list list * Pattern.inhabit_hint list) HintMap.t;
  files : string list;
}

(** The empty environment *)
let empty = {
  constants = [];
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

let general_hints (key1, key2, key3) {general=keys} =
  let search3 k1 k2 =
    match key3 with
    | Some _ -> snd (find3 (k1, k2, key3) keys) @ snd (find3 (k1, k2, None) keys)
    | None -> snd (find3 (k1, k2, None) keys)
  in
  let search2 k1 =
    match key2 with
    | Some _ -> search3 k1 key2 @ (search3 k1 None)
    | None -> search3 k1 None
  in
  let search1 =
    match key1 with
    | Some _ -> search2 key1 @ (search2 None)
    | None -> search2 None
  in search1

let inhabit_hints key {inhabit=hints} = snd @@ find key hints

let bound_names {bound=lst} = List.map fst lst

let constants {constants=lst} =
  List.map (fun (x, (yts, _)) -> (x, List.length yts)) lst

let used_names env =
  List.map fst env.bound @ List.map fst env.constants

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

let is_bound x env =
  match lookup_constant x env with
  | None -> false
  | Some _ -> true

let add_constant x ytsu env =
  if is_bound x env
  then Error.runtime "%t already exists" (Name.print_ident x)
  else { env with constants = (x, ytsu) :: env.constants }

let add_beta (key, hint) env =
  { env with
    beta =
      let tags, hints = find key env.beta in
      HintMap.add key ([] :: tags, hint :: hints) env.beta
  }

let add_betas xshs env =
  { env with
    beta =
      List.fold_left
        (fun db (xs, (key, h)) ->
           let tags, hints = find key db in
           HintMap.add key (xs :: tags, h :: hints) db)
        env.beta xshs
  }

let add_etas xshs env =
  { env with
    eta =
      List.fold_left
        (fun db (xs, (key, h)) ->
           let tags, hints = find key db in
           HintMap.add key (xs :: tags, h :: hints) db)
        env.eta xshs
  }

let add_generals xshs env =
  { env with
    general =
      List.fold_left
        (fun db (xs, (key, h)) ->
             let tags, hints = find3 key db in
             GeneralMap.add key (xs :: tags, h :: hints) db)
        env.general xshs
  }

let add_inhabits xshs env =
  { env with
    inhabit =
      List.fold_left
        (fun db (xs, (key, h)) ->
           let tags, hints = find key db in
           HintMap.add key (xs :: tags, h :: hints) db)
        env.inhabit xshs
  }

let unhint untags env =
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
  { env with
    beta = HintMap.map f env.beta ;
    eta = HintMap.map f env.eta ;
    general = GeneralMap.map f env.general ;
    inhabit = HintMap.map f env.inhabit ;
  }

let add_bound x v env =
  { env with bound = (x, v) :: env.bound }

(** generate a fresh atom of type [t] and bind it to [x]
    NB: This is an effectful computation. *)
let add_fresh ~loc env x (ctx, t) =
  let y, ctx = Context.cone ctx x t in
  let yt = Value.Term (ctx, Tt.mk_atom ~loc y, t) in
  let env = add_bound x yt env in
  y, env

let add_file f env =
  { env with files = (Filename.basename f) :: env.files }

let included f { files } = List.mem (Filename.basename f) files

let print env ppf =
  let forbidden_names = used_names env in
  Print.print ppf "---ENVIRONMENT---@." ;
  List.iter
    (fun (x, t) ->
     Print.print ppf "@[<hov 4>Parameter %t@;<1 -2>%t@]@\n" (Name.print_ident x)
       (Tt.print_constsig forbidden_names t))
    (List.rev env.constants) ;
  Print.print ppf "-----END-----@."

exception Match_fail

let match_tt_pattern env xvs p ctx e t =
  assert false

let match_pattern env xs p v =
  (* collect values of pattern variables *)
  let rec collect xvs (p,_) v =
    match p, v with 
    | Syntax.Patt_Anonymous, _ -> xvs

    | Syntax.Patt_Var k, v ->
       begin try
           let v' = List.assoc k xvs in
           if Value.equal_value v v'
           then xvs
           else raise Match_fail
         with Not_found -> (k,v) :: xvs
       end

    | Syntax.Patt_Bound k, v ->
       let v' = lookup_bound k env in
       if Value.equal_value v v'
       then xvs
       else raise Match_fail

    | Syntax.Patt_Jdg (pe, pt), Value.Term (ctx, e, ((Tt.Ty (t', loc)) as t)) ->
       let xvs = match_tt_pattern env xvs pt ctx t' (Tt.mk_type_ty ~loc) in
       match_tt_pattern env xvs pe ctx e t

    | Syntax.Patt_Tag (tag, ps), Value.Tag (tag', vs) when Name.eq_ident tag tag' ->
       let rec fold xvs = function
         | [], [] -> xvs
         | p::ps, v::vs ->
            let xvs = collect xvs p v in
            fold xvs (ps, vs)
         | ([], _::_ | _::_, []) ->
            raise Match_fail
       in
       fold xvs (ps, vs)

    | Syntax.Patt_Jdg _, (Value.Ty _ | Value.Closure _ | Value.Handler _ | Value.Tag _)
    | Syntax.Patt_Tag _, (Value.Term _ | Value.Ty _ | Value.Closure _ | Value.Handler _ | Value.Tag _) ->
       raise Match_fail
  in
  try
    let xvs = collect [] p v in
    let (_, env) =
      List.fold_left
        (fun (k, env) x ->
         let v = List.assoc k xvs in
         (k - 1, add_bound x v env))
        (List.length xs - 1, env)
        xs
    in
    Some env
  with Match_fail -> None
  

