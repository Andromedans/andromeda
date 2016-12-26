
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

let rec collect_tt_pattern env xvs p j =
  let loc = p.Location.loc in
  match p.Location.thing, Jdg.shape j with
  | Pattern.Tt_Anonymous, _ -> xvs

  | Pattern.Tt_As (p,k), _ ->
     let v = Runtime.mk_term j in
     let xvs = update k v xvs in
     collect_tt_pattern env xvs p j

  | Pattern.Tt_Bound k, _ ->
     let v' = Runtime.get_bound ~loc k env in
     if Runtime.equal_value (Runtime.mk_term j) v'
     then xvs
     else raise Match_fail

  | Pattern.Tt_Type, Jdg.Type ->
     xvs

  | Pattern.Tt_Constant x, Jdg.Constant y ->
     if Name.eq_ident x y
     then xvs
     else raise Match_fail

  | Pattern.Tt_Lambda (x,bopt,popt,p), Jdg.Lambda (jy,je) ->
     let xvs = begin match popt with
       | Some pt -> collect_tt_pattern env xvs pt (Jdg.term_of_ty (Jdg.atom_ty jy))
       | None -> xvs
     end in
     let yt = Runtime.mk_term (Jdg.atom_term ~loc jy) in
     let env = Runtime.push_bound yt env in
     let xvs = match bopt with
       | None -> xvs
       | Some k -> update k yt xvs
     in
     collect_tt_pattern env xvs p je

  | Pattern.Tt_Apply (p1,p2), Jdg.Apply (je1,je2) ->
    let xvs = collect_tt_pattern env xvs p1 je1 in
    let xvs = collect_tt_pattern env xvs p2 je2 in
    xvs

  | Pattern.Tt_Prod (x,bopt,popt,p), Jdg.Prod (jy,jb) ->
     let xvs = begin match popt with
       | Some pt -> collect_tt_pattern env xvs pt (Jdg.term_of_ty (Jdg.atom_ty jy))
       | None -> xvs
     end in
     let yt = Runtime.mk_term (Jdg.atom_term ~loc jy) in
     let env = Runtime.push_bound yt env in
     let xvs = match bopt with
       | None -> xvs
       | Some k -> update k yt xvs
     in
     collect_tt_pattern env xvs p (Jdg.term_of_ty jb)

  | Pattern.Tt_Eq (p1,p2), Jdg.Eq (je1,je2) ->
     let xvs = collect_tt_pattern env xvs p1 je1 in
     let xvs = collect_tt_pattern env xvs p2 je2 in
     xvs

  | Pattern.Tt_Refl p, Jdg.Refl je ->
     collect_tt_pattern env xvs p je

  | Pattern.Tt_GenAtom p, Jdg.Atom x ->
    let j = Jdg.atom_term ~loc x in
    collect_tt_pattern env xvs p j

  | Pattern.Tt_GenConstant p, Jdg.Constant c ->
    let signature = Runtime.get_typing_signature env in
    let j = Jdg.form ~loc signature (Jdg.Constant c) in
    collect_tt_pattern env xvs p j

  | (Pattern.Tt_Type | Pattern.Tt_Constant _ | Pattern.Tt_Apply _
     | Pattern.Tt_Lambda _ | Pattern.Tt_Prod _
     | Pattern.Tt_Eq _ | Pattern.Tt_Refl _
     | Pattern.Tt_GenAtom _ | Pattern.Tt_GenConstant _) , _ ->
     raise Match_fail

and collect_pattern env xvs {Location.thing=p;loc} v =
  match p, v with
  | Pattern.Patt_Anonymous, _ -> xvs

  | Pattern.Patt_As (p,k), v ->
     let xvs = update k v xvs in
     collect_pattern env xvs p v

  | Pattern.Patt_Bound k, v ->
     let v' = Runtime.get_bound ~loc k env in
     if Runtime.equal_value v v'
     then xvs
     else raise Match_fail

  | Pattern.Patt_Jdg (pe, pt), Runtime.Term j ->
     let xvs = collect_tt_pattern env xvs pt (Jdg.term_of_ty (Jdg.typeof j)) in
     collect_tt_pattern env xvs pe j

  | Pattern.Patt_Constructor (tag, ps), Runtime.Tag (tag', vs) when Name.eq_ident tag tag' ->
    multicollect_pattern env xvs ps vs

  | Pattern.Patt_Tuple ps, Runtime.Tuple vs ->
    multicollect_pattern env xvs ps vs

  | Pattern.Patt_Jdg _, (Runtime.Closure _ | Runtime.Handler _ |
                         Runtime.Tag _ | Runtime.Ref _ | Runtime.Dyn _|
                         Runtime.Tuple _ | Runtime.String _)
  | Pattern.Patt_Constructor _, (Runtime.Term _ | Runtime.Closure _ |
                                 Runtime.Handler _ | Runtime.Tag _ |
                                 Runtime.Ref _ | Runtime.Dyn _ |
                                 Runtime.Tuple _ | Runtime.String _)
  | Pattern.Patt_Tuple _, (Runtime.Term _ | Runtime.Closure _ |
                           Runtime.Handler _ | Runtime.Tag _ |
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

let match_pattern p v =
  (* collect values of pattern variables *)
  Runtime.get_env >>= fun env ->
  let r = begin try
    let xvs = collect_pattern env [] p v in
    (* return in decreasing de bruijn order: ready to fold with add_bound *)
    let xvs = List.sort (fun (k,_) (k',_) -> compare k k') xvs in
    let xvs = List.rev_map snd xvs in
    Some xvs
  with Match_fail -> None
  end in
  return r

let match_op_pattern ps pt vs checking =
  Runtime.get_env >>= fun env ->
  let r = begin try
    let xvs = multicollect_pattern env [] ps vs in
    let xvs = match pt with
      | None -> xvs
      | Some p ->
        let v = match checking with
          | Some j -> Predefined.from_option (Some (Runtime.mk_term (Jdg.term_of_ty j)))
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
