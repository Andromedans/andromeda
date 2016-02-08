
let (>>=) = Value.bind
let return = Value.return

(** Matching *)

exception Match_fail

let update k v xvs =
  try
    let v' = List.assoc k xvs in
    if Value.equal_value v v'
    then xvs
    else raise Match_fail
  with
    Not_found ->
      (k,v) :: xvs

let rec collect_tt_pattern env xvs (p',_) ctx ({Tt.term=e';loc;_} as e) t =
  match p', e' with
  | Syntax.Tt_Anonymous, _ -> xvs

  | Syntax.Tt_As (p,k), _ ->
     let v = Value.mk_term (Jdg.mk_term ctx e t) in
     let xvs = update k v xvs in
     collect_tt_pattern env xvs p ctx e t

  | Syntax.Tt_Bound k, _ ->
     let v' = Value.get_bound ~loc k env in
     if Value.equal_value (Value.mk_term (Jdg.mk_term ctx e t)) v'
     then xvs
     else raise Match_fail

  | Syntax.Tt_Type, Tt.Type ->
     xvs

  | Syntax.Tt_Constant x, Tt.Constant y ->
     if Name.eq_ident x y
     then xvs
     else raise Match_fail

  | Syntax.Tt_Lambda (x,bopt,popt,p), Tt.Lambda ((x',ty),(te,out)) ->
     let Tt.Ty t = ty in
     let {Tt.loc=loc;_} = t in
     let xvs = begin match popt with
       | Some pt -> collect_tt_pattern env xvs pt ctx t (Tt.mk_type_ty ~loc)
       | None -> xvs
     end in
     let y, ctx = Context.add_fresh ctx x ty in
     let yt = Value.mk_term (Jdg.mk_term ctx (Tt.mk_atom ~loc y) ty) in
     let env = Value.push_bound x yt env in
     let te = Tt.unabstract [y] te in
     let out = Tt.unabstract_ty [y] out in
     let xvs = match bopt with
       | None -> xvs
       | Some k -> update k yt xvs
     in
     collect_tt_pattern env xvs p ctx te out

  | Syntax.Tt_Apply (p1,p2), Tt.Apply (e1,((x,a),b),e2) ->
    let prod = Tt.mk_prod_ty ~loc x a b in
    let xvs = collect_tt_pattern env xvs p1 ctx e1 prod in
    let xvs = collect_tt_pattern env xvs p2 ctx e2 a in
    xvs

  | Syntax.Tt_Prod (x,bopt,popt,p), Tt.Prod ((x',ty),out) ->
     let Tt.Ty t = ty in
     let {Tt.loc=loc;_} = t in
     let xvs = begin match popt with
       | Some pt -> collect_tt_pattern env xvs pt ctx t (Tt.mk_type_ty ~loc)
       | None -> xvs
     end in
     let y, ctx = Context.add_fresh ctx x ty in
     let yt = Value.mk_term (Jdg.mk_term ctx (Tt.mk_atom ~loc y) ty) in
     let env = Value.push_bound x yt env in
     let Tt.Ty out = Tt.unabstract_ty [y] out in
     let xvs = match bopt with
       | None -> xvs
       | Some k -> update k yt xvs
     in
     collect_tt_pattern env xvs p ctx out (Tt.mk_type_ty ~loc:(e.Tt.loc))

  | Syntax.Tt_Eq (p1,p2), Tt.Eq (ty,te1,te2) ->
     let xvs = collect_tt_pattern env xvs p1 ctx te1 ty in
     let xvs = collect_tt_pattern env xvs p2 ctx te2 ty in
     xvs

  | Syntax.Tt_Refl p, Tt.Refl (ty,te) ->
     collect_tt_pattern env xvs p ctx te ty

  | Syntax.Tt_Signature s1, Tt.Signature (s2,shares) ->
     if not (Name.eq_ident s1 s2 && shares = [])
     then raise Match_fail
     else xvs

  | Syntax.Tt_Structure (s1, ps), Tt.Structure ((s2,shares), es) ->
     if not (Name.eq_ident s1 s2 && shares = [])
     then raise Match_fail
     else
       begin
         match Value.get_signature s1 env with
         | None -> Error.impossible ~loc "matching: unknown signature %t" (Name.print_ident s1)
         | Some s_def ->
            let rec fold xvs vs fields ps es =
              match fields, ps, es with
              | [], [], [] -> xvs
              | (_,_,t)::fields, p::ps, e::es ->
                 let t = Tt.instantiate_ty vs t in
                 let xvs = collect_tt_pattern env xvs p ctx e t in
                 fold xvs (e::vs) fields ps es
              | _, _, _ -> Error.impossible ~loc "matching: field mismatch in structure"
         in
         fold xvs [] s_def ps es
       end

  | Syntax.Tt_Projection (p,l), Tt.Projection (te,s,l') ->
     if Name.eq_ident l l'
     then
       collect_tt_pattern env xvs p ctx te (Tt.mk_signature_ty ~loc s)
     else raise Match_fail

  | Syntax.Tt_GenSig p, Tt.Signature (s,shares) ->
    begin match Value.get_signature s env with
      | Some s_def ->
        (* first build a representation of the signature definition *)
        let rec fold ctx nones res ys = function
          | [] ->
            let js = Jdg.term_of_ty (Jdg.mk_ty Context.empty (Tt.mk_signature_ty ~loc (s,List.rev nones))) in
            Value.mk_tuple [Value.mk_term js;Value.from_list (List.rev res)]
          | (l,x,t)::rem ->
            let t = Tt.unabstract_ty ys t in
            let y,ctx = Context.add_fresh ctx x t in
            let jy = Jdg.mk_term ctx (Tt.mk_atom ~loc y) t in
            let v = Value.mk_tuple [Value.mk_ident l;Value.mk_term jy] in
            fold ctx ((x,None)::nones) (v::res) (y::ys) rem
        in
        let vbase = fold Context.empty [] [] [] s_def in
        (* Build a representation of the constraints *)
        let rec fold ctx lv es ys = function
          | [] ->
            let lv = Value.from_list (List.rev lv) in
            Value.mk_tuple [vbase;lv]
          | ((_,_,t),(x,None))::rem ->
            let t = Tt.instantiate_ty es t in
            let y,ctx = Context.add_fresh ctx x t in
            let y = Tt.mk_atom ~loc y in
            let jy = Jdg.mk_term ctx y t in
            let v = Value.from_sum (Value.Inl (Value.mk_term jy)) in
            fold ctx (v::lv) (y::es) (y::ys) rem
          | ((_,_,t),(_,Some e))::rem ->
            let t = Tt.instantiate_ty es t
            and e = Tt.instantiate ys e in
            let je = Jdg.mk_term ctx e t in
            let v = Value.from_sum (Value.Inr (Value.mk_term je)) in
            fold ctx (v::lv) (e::es) ys rem
        in
        let v = fold ctx [] [] [] (List.combine s_def shares) in
        collect_pattern env xvs p v

      | None -> Error.impossible ~loc "matching unknown signature %t" (Name.print_ident s)
    end

  | Syntax.Tt_GenStruct (p,lp), Tt.Structure ((s,_) as str) ->
    let xvs = collect_tt_pattern env xvs p ctx (Tt.mk_signature ~loc s) Tt.typ in
    begin match Value.get_signature (fst s) env with
      | Some s_def ->
        (* build the list of explicit terms
           [es] instantiate the types, [exs] the constraints *)
        let rec fold vs es exs = function
          | [] -> Value.from_list (List.rev vs)
          | ((_,_,t),e)::rem ->
            let t = Tt.instantiate_ty es t
            and e,exs = match e with
              | Tt.Explicit e -> e,e::exs
              | Tt.Shared e -> Tt.instantiate exs e,exs
            in
            let je = Jdg.mk_term ctx e t in
            let v = Value.mk_term je in
            fold (v::vs) (e::es) exs rem
        in
        let lv = fold [] [] [] (List.combine s_def (Tt.struct_combine ~loc str)) in
        collect_pattern env xvs lp lv

      | None -> Error.impossible ~loc "matching structure of unknown signature %t" (Name.print_ident (fst s))
    end

  | Syntax.Tt_GenProj (p,pl), Tt.Projection (e,s,l) ->
    let vl = Value.mk_ident l in
    let xvs = collect_pattern env xvs pl vl in
    collect_tt_pattern env xvs p ctx e (Tt.mk_signature_ty ~loc s)

  | Syntax.Tt_GenAtom, Tt.Atom _ -> xvs

  | (Syntax.Tt_Type | Syntax.Tt_Constant _ | Syntax.Tt_Apply _
     | Syntax.Tt_Lambda _ | Syntax.Tt_Prod _
     | Syntax.Tt_Eq _ | Syntax.Tt_Refl _
     | Syntax.Tt_Signature _ | Syntax.Tt_Structure _
     | Syntax.Tt_Projection _
     | Syntax.Tt_GenSig _ | Syntax.Tt_GenStruct _ | Syntax.Tt_GenProj _
     | Syntax.Tt_GenAtom) , _ ->
     raise Match_fail

and collect_pattern env xvs (p,loc) v =
  match p, v with 
  | Syntax.Patt_Anonymous, _ -> xvs

  | Syntax.Patt_As (p,k), v ->
     let xvs = update k v xvs in
     collect_pattern env xvs p v

  | Syntax.Patt_Bound k, v ->
     let v' = Value.get_bound ~loc k env in
     if Value.equal_value v v'
     then xvs
     else raise Match_fail

  | Syntax.Patt_Jdg (pe, pt), Value.Term (Jdg.Term (ctx, e, t)) ->
     let Tt.Ty t' = t in
     let {Tt.loc=loc;_} = t' in
     let xvs = collect_tt_pattern env xvs pt ctx t' (Tt.mk_type_ty ~loc) in
     collect_tt_pattern env xvs pe ctx e t

  | Syntax.Patt_Data (tag, ps), Value.Tag (tag', vs) when Name.eq_ident tag tag' ->
    multicollect_pattern env xvs ps vs

  | Syntax.Patt_Nil, Value.List [] ->
    xvs

  | Syntax.Patt_Cons (p1,p2), Value.List (v1::v2) ->
    let xvs = collect_pattern env xvs p1 v1 in
    let xvs = collect_pattern env xvs p2 (Value.from_list v2) in
    xvs

  | Syntax.Patt_Tuple ps, Value.Tuple vs ->
    multicollect_pattern env xvs ps vs

  | Syntax.Patt_Jdg _, (Value.Closure _ | Value.Handler _ |
                        Value.Tag _ | Value.Ref _ | Value.List _ | Value.Tuple _ | Value.String _ | Value.Ident _)
  | Syntax.Patt_Data _, (Value.Term _ | Value.Closure _ |
                        Value.Handler _ | Value.Tag _ | Value.Ref _ | Value.List _ | Value.Tuple _ | Value.String _ | Value.Ident _)
  | Syntax.Patt_Nil, (Value.Term _ | Value.Closure _ |
                        Value.Handler _ | Value.Tag _ | Value.Ref _ | Value.List (_::_) | Value.Tuple _ | Value.String _ | Value.Ident _)
  | Syntax.Patt_Cons _, (Value.Term _ | Value.Closure _ |
                        Value.Handler _ | Value.Tag _ | Value.Ref _ | Value.List [] | Value.Tuple _ | Value.String _ | Value.Ident _)
  | Syntax.Patt_Tuple _, (Value.Term _ | Value.Closure _ | Value.Handler _ | Value.Tag _ | Value.Ref _ |
                          Value.List _ | Value.String _ | Value.Ident _) ->
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
  Value.get_env >>= fun env ->
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
  Value.get_env >>= fun env ->
  let r = begin try
    let xvs = multicollect_pattern env [] ps vs in
    let xvs = match pt, checking with
      | None, (None | Some _) -> xvs
      | Some p, Some (Jdg.Ty (ctx,Tt.Ty t)) ->
        collect_tt_pattern env xvs p ctx t Tt.typ
      | Some _, None -> raise Match_fail
    in
    (* return in decreasing de bruijn order: ready to fold with add_bound *)
    let xvs = List.sort (fun (k,_) (k',_) -> compare k k') xvs in
    let xvs = List.rev_map snd xvs in
    Some xvs
  with Match_fail -> None
  end in
  return r

