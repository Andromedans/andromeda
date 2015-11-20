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
  handle : (string * (Name.ident * Syntax.comp)) list;
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
  handle = [] ;
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

let add_handle op xc env =
  { env with handle = (op, xc) :: env.handle }

let lookup_handle op {handle=lst} =
  try
    Some (List.assoc op lst)
  with Not_found -> None

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

let application_pop (e,loc) = match e with
  | Tt.Spine (lhs,(absl,out),rhs) ->
    let rec fold es xts = function
      | [x,tx], [e2] ->
        let xts = List.rev xts in
        let u = Tt.mk_prod_ty ~loc [x,tx] out in
        let e1 = Tt.mk_spine ~loc lhs xts u (List.rev es) in
        let t1 = Tt.instantiate_ty es u in
        let t2 = Tt.instantiate_ty es tx in
        e1,t1,e2,t2
      | (x,tx)::absl, e::rhs ->
        fold (e::es) ((x,tx)::xts) (absl, rhs)
      | [],[] | [],_::_ | _::_,[] -> Error.impossible ~loc "impossible spine encountered in application_pop"
      in
    fold [] [] (absl,rhs)
  | _ -> raise Match_fail

let rec collect_tt_pattern env xvs (p',_) ctx ((e',_) as e) t =
  match p', e' with
    | Syntax.Tt_Anonymous, _ -> xvs

    | Syntax.Tt_As (p,k), _ ->
      let v = Value.Term (ctx,e,t) in
      let xvs = try
          let v' = List.assoc k xvs in
          if Value.equal_value v v'
          then xvs
          else raise Match_fail
        with | Not_found ->
          (k,v) :: xvs
        in
      collect_tt_pattern env xvs p ctx e t

    | Syntax.Tt_Bound k, _ ->
      let v' = lookup_bound k env in
      if Value.equal_value (Value.Term (ctx,e,t)) v'
      then xvs
      else raise Match_fail

    | Syntax.Tt_Type, Tt.Type ->
      xvs

    | Syntax.Tt_Constant x, Tt.Constant (y,lst) ->
      if lst = [] && Name.eq_ident x y
      then xvs
      else raise Match_fail

    | Syntax.Tt_Lambda (x,bopt,popt,p), Tt.Lambda ((x',ty)::abs,(te,out)) ->
      let Tt.Ty t = ty in let _,loc = t in
      let xvs = match popt with
        | Some pt -> collect_tt_pattern env xvs pt ctx t (Tt.mk_type_ty ~loc)
        | None -> xvs
        in
      let y, ctx = Context.cone ctx x ty in
      let yt = Value.Term (ctx, Tt.mk_atom ~loc y, ty) in
      let env = add_bound x yt env in
      let te = Tt.mk_lambda ~loc:(snd e) abs te out in
      let te = Tt.unabstract [y] te in
      let t = Tt.mk_prod_ty ~loc:(snd e) abs out in
      let t = Tt.unabstract_ty [y] t in
      let xvs = match bopt with
        | None -> xvs
        | Some k ->
          begin try
            let v' = List.assoc k xvs in
            if Value.equal_value yt v'
            then xvs
            else raise Match_fail
          with
            | Not_found -> (k,yt)::xvs
          end
        in
      let xvs = collect_tt_pattern env xvs p ctx te t in
      xvs

    | Syntax.Tt_App (p1,p2), _ ->
      let te1, ty1, te2, ty2 = application_pop e in
      let xvs = collect_tt_pattern env xvs p1 ctx te1 ty1 in
      let xvs = collect_tt_pattern env xvs p2 ctx te2 ty2 in
      xvs

    | Syntax.Tt_Prod (x,bopt,popt,p), Tt.Prod ((x',ty)::abs,out) ->
      let Tt.Ty t = ty in let _,loc = t in
      let xvs = match popt with
        | Some pt -> collect_tt_pattern env xvs pt ctx t (Tt.mk_type_ty ~loc)
        | None -> xvs
        in
      let y, ctx = Context.cone ctx x ty in
      let yt = Value.Term (ctx, Tt.mk_atom ~loc y, ty) in
      let env = add_bound x yt env in
      let t = Tt.mk_prod ~loc:(snd e) abs out in
      let t = Tt.unabstract [y] t in
      let xvs = match bopt with
        | None -> xvs
        | Some k ->
          begin try
            let v' = List.assoc k xvs in
            if Value.equal_value yt v'
            then xvs
            else raise Match_fail
          with
            | Not_found -> (k,yt)::xvs
          end
        in
      let xvs = collect_tt_pattern env xvs p ctx t (Tt.mk_type_ty ~loc:(snd e)) in
      xvs

    | Syntax.Tt_Eq (p1,p2), Tt.Eq (ty,te1,te2) ->
      let xvs = collect_tt_pattern env xvs p1 ctx te1 ty in
      let xvs = collect_tt_pattern env xvs p2 ctx te2 ty in
      xvs

    | Syntax.Tt_Refl p, Tt.Refl (ty,te) ->
      let xvs = collect_tt_pattern env xvs p ctx te ty in
      xvs

    | Syntax.Tt_Inhab, Tt.Inhab _ ->
      xvs

    | Syntax.Tt_Bracket p, Tt.Bracket (Tt.Ty ty) ->
      let _,loc = ty in
      let xvs = collect_tt_pattern env xvs p ctx ty (Tt.mk_type_ty ~loc) in
      xvs

    | Syntax.Tt_Signature xps, Tt.Signature xts ->
      let rec fold env xvs ys ctx xps xts =
        match xps, xts with
          | [], [] ->
            xvs
          | (l,x,bopt,p)::xps, (l',x',t)::xts ->
            if Name.eq_ident l l'
            then
              let t = Tt.unabstract_ty ys t in
              let Tt.Ty t' = t in let (_, loc) = t' in
              let xvs = collect_tt_pattern env xvs p ctx t' (Tt.mk_type_ty ~loc) in
              let y, ctx = Context.cone ctx x t in
              let yt = Value.Term (ctx, Tt.mk_atom ~loc y, t) in
              let env = add_bound x yt env in
              let xvs = match bopt with
                | None -> xvs
                | Some k ->
                  begin try
                    let v' = List.assoc k xvs in
                    if Value.equal_value yt v'
                    then xvs
                    else raise Match_fail
                  with
                    | Not_found -> (k,yt)::xvs
                  end
                in
              fold env xvs (y::ys) ctx xps xts
            else raise Match_fail
          | _::_, [] | [], _::_ ->
            raise Match_fail
        in
      fold env xvs [] ctx xps xts

    | Syntax.Tt_Structure xps, Tt.Structure xts ->
      let rec fold env xvs ys ctx xps xts =
        match xps, xts with
          | [], [] ->
            xvs
          | (l,x,bopt,p)::xps, (l',x',t,te)::xts ->
            if Name.eq_ident l l'
            then
              let t = Tt.unabstract_ty ys t in
              let te = Tt.unabstract ys te in
              let xvs = collect_tt_pattern env xvs p ctx te t in
              let y, ctx = Context.cone ctx x t in
              let Tt.Ty (_,loc) = t in
              let yt = Value.Term (ctx, Tt.mk_atom ~loc y, t) in
              let env = add_bound x yt env in
              let xvs = match bopt with
                | None -> xvs
                | Some k ->
                  begin try
                    let v' = List.assoc k xvs in
                    if Value.equal_value yt v'
                    then xvs
                    else raise Match_fail
                  with
                    | Not_found -> (k,yt)::xvs
                  end
                in
              fold env xvs (y::ys) ctx xps xts
            else raise Match_fail
          | _::_, [] | [], _::_ ->
            raise Match_fail
        in
      fold env xvs [] ctx xps xts

    | Syntax.Tt_Projection (p,l), Tt.Projection (te,xts,l') ->
      if Name.eq_ident l l'
      then
        let _,loc = e in
        let xvs = collect_tt_pattern env xvs p ctx te (Tt.mk_signature_ty ~loc xts) in
        xvs
      else raise Match_fail

    | (Syntax.Tt_Type | Syntax.Tt_Constant _ | Syntax.Tt_Lambda _
        | Syntax.Tt_Prod _ | Syntax.Tt_Eq _ | Syntax.Tt_Refl _ | Syntax.Tt_Inhab
        | Syntax.Tt_Bracket _ | Syntax.Tt_Signature _ | Syntax.Tt_Structure _
        | Syntax.Tt_Projection _) , _ ->
      raise Match_fail


let match_pattern env xs p v =
  (* collect values of pattern variables *)
  let rec collect xvs (p,_) v =
    match p, v with 
    | Syntax.Patt_Anonymous, _ -> xvs

    | Syntax.Patt_As (p,k), v ->
       let xvs = try
           let v' = List.assoc k xvs in
           if Value.equal_value v v'
           then xvs
           else raise Match_fail
         with Not_found -> (k,v) :: xvs
         in
       collect xvs p v

    | Syntax.Patt_Bound k, v ->
       let v' = lookup_bound k env in
       if Value.equal_value v v'
       then xvs
       else raise Match_fail

    | Syntax.Patt_Jdg (pe, pt), Value.Term (ctx, e, t) ->
       let Tt.Ty t' = t in
       let _,loc = t' in
       let xvs = collect_tt_pattern env xvs pt ctx t' (Tt.mk_type_ty ~loc) in
       collect_tt_pattern env xvs pe ctx e t

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
  

