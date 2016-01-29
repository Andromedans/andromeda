
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
  match p.Location.thing, Jdg.shape ~loc (Runtime.get_typing_env env) j with
  | Syntax.Tt_Anonymous, _ -> xvs

  | Syntax.Tt_As (p,k), _ ->
     let v = Runtime.mk_term j in
     let xvs = update k v xvs in
     collect_tt_pattern env xvs p j

  | Syntax.Tt_Bound k, _ ->
     let v' = Runtime.get_bound ~loc k env in
     if Runtime.equal_value (Runtime.mk_term j) v'
     then xvs
     else raise Match_fail

  | Syntax.Tt_Type, Jdg.Type ->
     xvs

  | Syntax.Tt_Constant x, Jdg.Constant y ->
     if Name.eq_ident x y
     then xvs
     else raise Match_fail

  | Syntax.Tt_Lambda (x,bopt,popt,p), Jdg.Lambda (jy,je) ->
     let xvs = begin match popt with
       | Some pt -> collect_tt_pattern env xvs pt (Jdg.term_of_ty (Jdg.atom_ty jy))
       | None -> xvs
     end in
     let yt = Runtime.mk_term (Jdg.atom_term ~loc jy) in
     let env = Runtime.push_bound x yt env in
     let xvs = match bopt with
       | None -> xvs
       | Some k -> update k yt xvs
     in
     collect_tt_pattern env xvs p je

  | Syntax.Tt_Apply (p1,p2), Jdg.Apply (je1,je2) ->
    let xvs = collect_tt_pattern env xvs p1 je1 in
    let xvs = collect_tt_pattern env xvs p2 je2 in
    xvs

  | Syntax.Tt_Prod (x,bopt,popt,p), Jdg.Prod (jy,jb) ->
     let xvs = begin match popt with
       | Some pt -> collect_tt_pattern env xvs pt (Jdg.term_of_ty (Jdg.atom_ty jy))
       | None -> xvs
     end in
     let yt = Runtime.mk_term (Jdg.atom_term ~loc jy) in
     let env = Runtime.push_bound x yt env in
     let xvs = match bopt with
       | None -> xvs
       | Some k -> update k yt xvs
     in
     collect_tt_pattern env xvs p (Jdg.term_of_ty jb)

  | Syntax.Tt_Eq (p1,p2), Jdg.Eq (je1,je2) ->
     let xvs = collect_tt_pattern env xvs p1 je1 in
     let xvs = collect_tt_pattern env xvs p2 je2 in
     xvs

  | Syntax.Tt_Refl p, Jdg.Refl je ->
     collect_tt_pattern env xvs p je

  | Syntax.Tt_Signature s1, Jdg.Signature (s2,shares) ->
     if not (Name.eq_ident s1 s2 &&
             List.for_all (function Tt.Unconstrained _ -> true | Tt.Constrained _ -> false) shares)
     then raise Match_fail
     else xvs

  | Syntax.Tt_Structure ps, Jdg.Structure (s, js) ->
    let s, shares = match Jdg.shape_ty ~loc:Location.unknown (Runtime.get_typing_env env) s with
      | Jdg.Signature s -> s
      | _ -> assert false
    in
    if not (List.for_all (function Tt.Unconstrained _ -> true | Tt.Constrained _ -> false) shares &&
            List.length ps = List.length js)
    then raise Match_fail
    else
      let s_def = Runtime.get_signature s env in
      let rec fold xvs = function
        | [] -> xvs
        | ((l1, p), (l2, j)) :: rem ->
          if not (Name.eq_ident l1 l2)
          then raise Match_fail
          else
            let xvs = collect_tt_pattern env xvs p j in
            fold xvs rem
      in
      let ljs = List.map2 (fun j (l, _, _) -> (l, j)) js s_def in
      fold xvs (List.combine ps ljs)

  | Syntax.Tt_Projection (p,l), Jdg.Projection (je,l') ->
     if Name.eq_ident l l'
     then collect_tt_pattern env xvs p je
     else raise Match_fail

  | Syntax.Tt_GenSig p, Jdg.Signature (s,shares) ->
    let bare = Tt.mk_signature ~loc (s, List.map (fun _ -> Tt.Unconstrained Name.anonymous) shares) in
    let bare = Jdg.mk_term Context.empty bare Tt.typ in
    let bare = Runtime.mk_term bare in
    let shares = List.map (function
        | Tt.Unconstrained y ->
          let jy = Jdg.atom_term ~loc y in
          Predefined.from_constrain (Tt.Unconstrained (Runtime.mk_term jy))
        | Tt.Constrained j ->
          Predefined.from_constrain (Tt.Constrained (Runtime.mk_term j)))
      shares
    in
    let shares = Predefined.mk_list shares in
    let v = Runtime.mk_tuple [bare;shares] in
    collect_pattern env xvs p v

  | Syntax.Tt_GenStruct (p,lp), Jdg.Structure (s, js) ->
    let xvs = collect_tt_pattern env xvs p (Jdg.term_of_ty s) in
    let v = Predefined.mk_list (List.map Runtime.mk_term js) in
    collect_pattern env xvs lp v

  | Syntax.Tt_GenProj (p,pl), Jdg.Projection (j,l) ->
    let vl = Runtime.mk_ident l in
    let xvs = collect_pattern env xvs pl vl in
    collect_tt_pattern env xvs p j

  | Syntax.Tt_GenAtom p, Jdg.Atom x ->
    let j = Jdg.atom_term ~loc x in
    collect_tt_pattern env xvs p j

  | Syntax.Tt_GenConstant p, Jdg.Constant c ->
    let t = Runtime.get_constant c env in
    let c = Tt.mk_constant ~loc c in
    let j = Jdg.mk_term Context.empty c t in
    collect_tt_pattern env xvs p j

  | (Syntax.Tt_Type | Syntax.Tt_Constant _ | Syntax.Tt_Apply _
     | Syntax.Tt_Lambda _ | Syntax.Tt_Prod _
     | Syntax.Tt_Eq _ | Syntax.Tt_Refl _
     | Syntax.Tt_Signature _ | Syntax.Tt_Structure _
     | Syntax.Tt_Projection _
     | Syntax.Tt_GenSig _ | Syntax.Tt_GenStruct _ | Syntax.Tt_GenProj _
     | Syntax.Tt_GenAtom _ | Syntax.Tt_GenConstant _) , _ ->
     raise Match_fail

and collect_pattern env xvs {Location.thing=p;loc} v =
  match p, v with 
  | Syntax.Patt_Anonymous, _ -> xvs

  | Syntax.Patt_As (p,k), v ->
     let xvs = update k v xvs in
     collect_pattern env xvs p v

  | Syntax.Patt_Bound k, v ->
     let v' = Runtime.get_bound ~loc k env in
     if Runtime.equal_value v v'
     then xvs
     else raise Match_fail

  | Syntax.Patt_Jdg (pe, pt), Runtime.Term j ->
     let xvs = collect_tt_pattern env xvs pt (Jdg.term_of_ty (Jdg.typeof j)) in
     collect_tt_pattern env xvs pe j

  | Syntax.Patt_Constructor (tag, ps), Runtime.Tag (tag', vs) when Name.eq_ident tag tag' ->
    multicollect_pattern env xvs ps vs

  | Syntax.Patt_Tuple ps, Runtime.Tuple vs ->
    multicollect_pattern env xvs ps vs

  | Syntax.Patt_Jdg _, (Runtime.Closure _ | Runtime.Handler _ |
                        Runtime.Tag _ | Runtime.Ref _ | Runtime.Tuple _ | Runtime.String _ | Runtime.Ident _)
  | Syntax.Patt_Constructor _, (Runtime.Term _ | Runtime.Closure _ |
                        Runtime.Handler _ | Runtime.Tag _ | Runtime.Ref _ | Runtime.Tuple _ | Runtime.String _ | Runtime.Ident _)
  | Syntax.Patt_Tuple _, (Runtime.Term _ | Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Ref _ |
                          Runtime.String _ | Runtime.Ident _) ->
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

