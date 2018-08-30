
let (>>=) = Runtime.bind
let return = Runtime.return

(** Matching *)

exception Match_fail

let update k v xvs =
  try
    let v' = List.assoc k xvs in
    if Runtime.equal_value v v'
    then xvs
    else raise Match_fail
  with
    Not_found ->
      (k,v) :: xvs

let rec collect_is_term env xvs p j =
  let loc = p.Location.loc in
  match p.Location.thing, Jdg.invert_is_term j with
  | Pattern.Term_Anonymous, _ -> xvs

  | Pattern.Term_As (p,k), _ ->
     let v = Runtime.mk_is_term j in
     let xvs = update k v xvs in
     collect_is_term env xvs p j

  | Pattern.Term_Bound k, _ ->
     let v' = Runtime.get_bound ~loc k env in
     if Runtime.equal_value (Runtime.mk_is_term j) v'
     then xvs
     else raise Match_fail

  | Pattern.Term_Constant x, Jdg.Constant y ->
     if Name.eq_ident x y
     then xvs
     else raise Match_fail

  | Pattern.Term_Abstract (x,bopt,popt,p), Jdg.Abstract (jy,je) ->
     let xvs = begin match popt with
       | Some pt -> collect_is_type env xvs pt (Jdg.atom_is_type jy)
       | None -> xvs
     end in
     let yt = Runtime.mk_is_term (Jdg.atom_is_term ~loc jy) in
     let env = Runtime.push_bound yt env in
     let xvs = match bopt with
       | None -> xvs
       | Some k -> update k yt xvs
     in
     collect_is_term env xvs p je

  | Pattern.Term_GenAtom p, Jdg.Atom x ->
    let j = Jdg.atom_is_term ~loc x in
    collect_is_term env xvs p j

  | Pattern.Term_GenConstant p, Jdg.Constant c ->
    let signature = Runtime.get_typing_signature env in
    let j = Jdg.form ~loc signature (Jdg.Constant c) in
    collect_is_term env xvs p j

  | (Pattern.Term_Constant _ | Pattern.Term_Abstract _ |
     Pattern.Term_GenAtom _ | Pattern.Term_GenConstant _) , _ ->
     raise Match_fail

and collect_is_type env xvs p j =
  let loc = p.Location.loc in
  match p.Location.thing, Jdg.invert_is_type j with

  | Pattern.Type_Anonymous, _ -> xvs

  | Pattern.Type_As (p,k), _ ->
     let v = Runtime.mk_is_type j in
     let xvs = update k v xvs in
     collect_is_type env xvs p j

  | Pattern.Type_Bound k, _ ->
     let v' = Runtime.get_bound ~loc k env in
     if Runtime.equal_value (Runtime.mk_is_type j) v'
     then xvs
     else raise Match_fail

  | Pattern.Type_Type, Jdg.Type ->
     xvs

  | Pattern.Type_AbstractTy (x,bopt,popt,p), Jdg.AbstractTy (jy,jb) ->
     let xvs = begin match popt with
       | Some pt -> collect_is_type env xvs pt (Jdg.atom_is_type jy)
       | None -> xvs
     end in
     let yt = Runtime.mk_is_term (Jdg.atom_is_term ~loc jy) in
     let env = Runtime.push_bound yt env in
     let xvs = match bopt with
       | None -> xvs
       | Some k -> update k yt xvs
     in
     collect_is_type env xvs p jb

  | Pattern.Type_El p, Jdg.El j ->
     collect_is_term env xvs p j

  | (Pattern.Type_Type | Pattern.Type_AbstractTy _ | Pattern.Type_El _), _ ->
     raise Match_fail

and collect_eq_type env xvs pt1 pt2 jeq =
  let (t1, t2) = Jdg.invert_eq_type jeq in
  let xvs = collect_is_type env xvs pt1 t1 in
  let xvs = collect_is_type env xvs pt2 t2 in
  xvs

and collect_eq_term env xvs p1 p2 pt jeq =
  let (e1, e2, t) = Jdg.invert_eq_term jeq in
  let xvs = collect_is_term env xvs p1 e1 in
  let xvs = collect_is_term env xvs p2 e2 in
  let xvs = collect_is_type env xvs pt t in
  xvs

and collect_pattern env xvs {Location.thing=p;loc} v =
  match p, v with
  | Pattern.Anonymous, _ -> xvs

  | Pattern.As (p,k), v ->
     let xvs = update k v xvs in
     collect_pattern env xvs p v

  | Pattern.Bound k, v ->
     let v' = Runtime.get_bound ~loc k env in
     if Runtime.equal_value v v'
     then xvs
     else raise Match_fail

  | Pattern.IsType pt, Runtime.IsType j ->
     collect_is_type env xvs pt j

  | Pattern.IsTerm (pe, pt), Runtime.IsTerm j ->
     let xvs = collect_is_type env xvs pt (Jdg.typeof j) in
     collect_is_term env xvs pe j

  | Pattern.EqType (pt1, pt2), Runtime.EqType j ->
     collect_eq_type env xvs pt1 pt2 j

  | Pattern.EqTerm (p1, p2, pt), Runtime.EqTerm j ->
     collect_eq_term env xvs p1 p2 pt j

  | Pattern.Constructor (tag, ps), Runtime.Tag (tag', vs) when Name.eq_ident tag tag' ->
    multicollect_pattern env xvs ps vs

  | Pattern.Tuple ps, Runtime.Tuple vs ->
    multicollect_pattern env xvs ps vs

  | Pattern.IsTerm _, (Runtime.IsType _ | Runtime.EqTerm _ | Runtime.EqType _ |
                       Runtime.Closure _ | Runtime.Handler _ |
                       Runtime.Tag _ | Runtime.Ref _ | Runtime.Dyn _|
                       Runtime.Tuple _ | Runtime.String _)

  | Pattern.IsType _, (Runtime.IsTerm _ | Runtime.EqTerm _ | Runtime.EqType _ |
                       Runtime.Closure _ | Runtime.Handler _ |
                       Runtime.Tag _ | Runtime.Ref _ | Runtime.Dyn _|
                       Runtime.Tuple _ | Runtime.String _)

  | Pattern.EqTerm _, (Runtime.IsTerm _ | Runtime.IsType _ | Runtime.EqType _ |
                       Runtime.Closure _ | Runtime.Handler _ |
                       Runtime.Tag _ | Runtime.Ref _ | Runtime.Dyn _|
                       Runtime.Tuple _ | Runtime.String _)

  | Pattern.EqType _, (Runtime.IsTerm _ | Runtime.IsType _ | Runtime.EqTerm _ |
                       Runtime.Closure _ | Runtime.Handler _ |
                       Runtime.Tag _ | Runtime.Ref _ | Runtime.Dyn _|
                       Runtime.Tuple _ | Runtime.String _)

  | Pattern.Constructor _, (Runtime.IsTerm _ | Runtime.IsType _ | Runtime.EqTerm _ | Runtime.EqType _ |
                            Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ |
                            Runtime.Ref _ | Runtime.Dyn _ |
                            Runtime.Tuple _ | Runtime.String _)

  | Pattern.Tuple _, (Runtime.IsTerm _ | Runtime.IsType _ | Runtime.EqTerm _ | Runtime.EqType _ |
                      Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ |
                      Runtime.Ref _ | Runtime.Dyn _ | Runtime.String _) ->
     raise Match_fail

and multicollect_pattern env xvs ps vs =
  let rec fold xvs = function
    | [], [] -> xvs
    | p::ps, v::vs ->
      let xvs = collect_pattern env xvs p v in
      fold xvs (ps, vs)
    | ([], _::_ | _::_, []) ->
      raise Match_fail
  in
  fold xvs (ps, vs)

let match_pattern_env p v env =
  try
    let xvs = collect_pattern env [] p v in
    (* return in decreasing de bruijn order: ready to fold with add_bound *)
    let xvs = List.sort (fun (k,_) (k',_) -> compare k k') xvs in
    let xvs = List.rev_map snd xvs in
    Some xvs
  with
    Match_fail -> None

let top_match_pattern p v =
  let (>>=) = Runtime.top_bind in
  Runtime.top_get_env >>= fun env ->
    let r = match_pattern_env p v env  in
    Runtime.top_return r

let match_pattern p v =
  (* collect values of pattern variables *)
  Runtime.get_env >>= fun env ->
  let r = match_pattern_env p v env  in
  return r


let match_op_pattern ps pt vs checking =
  Runtime.get_env >>= fun env ->
  let r = begin try
    let xvs = multicollect_pattern env [] ps vs in
    let xvs = match pt with
      | None -> xvs
      | Some p ->
        let v = match checking with
          | Some j -> Predefined.from_option (Some (Runtime.mk_is_type j))
          | None -> Predefined.from_option None
       in
       collect_pattern env xvs p v
    in
    (* return in decreasing de bruijn order: ready to fold with add_bound *)
    let xvs = List.sort (fun (k,_) (k',_) -> compare k k') xvs in
    let xvs = List.rev_map snd xvs in
    Some xvs
  with Match_fail -> None
  end in
  return r
