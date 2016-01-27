
module AtomSet = Name.AtomSet

let (>>=) = Value.bind
let return = Value.return

let mk_abstractable ~loc ctx xs =
  let rec fold ctx abstracted zs es = function
    | [] ->
      return (ctx,zs,es)
    | x::xs ->
      begin match Context.lookup_ty x ctx with
        | None ->
          let abstracted = AtomSet.add x abstracted in
          fold ctx abstracted zs es xs
        | Some xty ->
          let rec xfold ctx zs' es' = function
            | [] ->
              let es = List.map (Tt.substitute zs' es') es in
              let zs = zs' @ zs and es = es' @ es in
              let abstracted = AtomSet.add x abstracted in
              fold ctx abstracted zs es xs
            | y::ys when (AtomSet.mem y abstracted) ->
              xfold ctx zs' es' ys
            | y::ys ->
              let yty = (match Context.lookup_ty y ctx with
                | Some ty -> ty
                | None -> Error.impossible
                  ~loc "cannot abstract %t as %t depends on it, but it does not appear in the context?"
                  (Name.print_atom x) (Name.print_atom y)) in
              let vx = Value.mk_term (Jdg.mk_term ctx (Tt.mk_atom ~loc x) xty)
              and vy = Value.mk_term (Jdg.mk_term ctx (Tt.mk_atom ~loc y) yty) in
              Value.perform_abstract vx vy >>= fun v ->
              begin match Value.as_option ~loc v with
                | None ->
                  Error.runtime ~loc "Cannot abstract %t because %t depends on it in context@ %t."
                  (Name.print_atom x) (Name.print_atom y) (Context.print ctx)
                | Some v ->
                  let Jdg.Term (ctxe,e,te) = Value.as_term ~loc v in
                  if Tt.alpha_equal_ty yty te
                  then
                    let ctx = Context.join ~loc ctx ctxe in
                    let ehyps = Tt.assumptions_term e in
                    if AtomSet.is_empty (AtomSet.inter ehyps (Context.needed_by ~loc x ctx))
                    then
                      let ctx = Context.substitute ~loc y (ctx,e,te) in
                      xfold ctx (y::zs') (e::es') ys
                    else
                      Error.runtime ~loc "When abstracting %t in context %t, cannot replace %t with %t: it depends on %t"
                        (Name.print_atom x) (Context.print ctx) (Name.print_atom y) (Tt.print_term [] e)
                        (Print.sequence Name.print_atom " " (Name.AtomSet.elements ehyps))
                  else
                    Error.runtime ~loc "When abstracting %t, cannot replace %t : %t with %t : %t (types are not equal)"
                      (Name.print_atom x)
                      (Name.print_atom y) (Tt.print_ty [] yty)
                      (Tt.print_term [] e) (Tt.print_ty [] te)
              end
          in
          let needed_by = Context.needed_by ~loc x ctx in
          let sorted = Context.sort ctx in
          xfold ctx [] [] (List.filter (fun x -> AtomSet.mem x needed_by) sorted)
      end
  in
  fold ctx AtomSet.empty [] [] xs


let context_abstract ~loc ctx xs ts =
  mk_abstractable ~loc ctx xs >>= fun (ctx,ys,es) ->
  let ctx = Context.abstract ~loc ctx xs ts in
  return (ctx,ys,es)

(** Matching *)

exception Match_fail

let rec collect_tt_pattern env xvs (p',_) ctx ({Tt.term=e';loc;_} as e) t =
  match p', e' with
  | Syntax.Tt_Anonymous, _ -> xvs

  | Syntax.Tt_As (p,k), _ ->
     let v = Value.mk_term (Jdg.mk_term ctx e t) in
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
     collect_tt_pattern env xvs p ctx out (Tt.mk_type_ty ~loc:(e.Tt.loc))

  | Syntax.Tt_Eq (p1,p2), Tt.Eq (ty,te1,te2) ->
     let xvs = collect_tt_pattern env xvs p1 ctx te1 ty in
     let xvs = collect_tt_pattern env xvs p2 ctx te2 ty in
     xvs

  | Syntax.Tt_Refl p, Tt.Refl (ty,te) ->
     collect_tt_pattern env xvs p ctx te ty

  | Syntax.Tt_Signature xps, Tt.Signature xts ->
     let rec fold env xvs ys ctx xps xts =
       match xps, xts with
       | [], [] ->
          xvs
       | (l,x,bopt,p)::xps, (l',x',t)::xts ->
          if Name.eq_ident l l'
          then
            let t = Tt.unabstract_ty ys t in
            let Tt.Ty t' = t in
            let {Tt.loc=loc;_} = t' in
            let xvs = collect_tt_pattern env xvs p ctx t' (Tt.mk_type_ty ~loc) in
            (* XXX should we use [add_abstracting] instead of [add_fresh]? *)
            let y, ctx = Context.add_fresh ctx x t in
            let yt = Value.mk_term (Jdg.mk_term ctx (Tt.mk_atom ~loc y) t) in
            let env = Value.push_bound x yt env in
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
            (* Should we use [add_abstracting] instead of [add_fresh]? *)
            let y, ctx = Context.add_fresh ctx x t in
            let Tt.Ty {Tt.loc=loc;_} = t in
            let yt = Value.mk_term (Jdg.mk_term ctx (Tt.mk_atom ~loc y) t) in
            let env = Value.push_bound x yt env in
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
       let {Tt.loc=loc;_} = e in
       let xvs = collect_tt_pattern env xvs p ctx te (Tt.mk_signature_ty ~loc xts) in
       xvs
     else raise Match_fail

  | (Syntax.Tt_Type | Syntax.Tt_Constant _ | Syntax.Tt_Apply _
     | Syntax.Tt_Lambda _ | Syntax.Tt_Prod _
     | Syntax.Tt_Eq _ | Syntax.Tt_Refl _
     | Syntax.Tt_Signature _ | Syntax.Tt_Structure _
     | Syntax.Tt_Projection _) , _ ->
     raise Match_fail

let rec collect_pattern env xvs (p,loc) v =
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

  | Syntax.Patt_Tag (tag, ps), Value.Tag (tag', vs) when Name.eq_ident tag tag' ->
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
                        Value.Tag _ | Value.Ref _ | Value.List _ | Value.Tuple _ | Value.String _)
  | Syntax.Patt_Tag _, (Value.Term _ | Value.Closure _ |
                        Value.Handler _ | Value.Tag _ | Value.Ref _ | Value.List _ | Value.Tuple _ | Value.String _)
  | Syntax.Patt_Nil, (Value.Term _ | Value.Closure _ |
                        Value.Handler _ | Value.Tag _ | Value.Ref _ | Value.List (_::_) | Value.Tuple _ | Value.String _)
  | Syntax.Patt_Cons _, (Value.Term _ | Value.Closure _ |
                        Value.Handler _ | Value.Tag _ | Value.Ref _ | Value.List [] | Value.Tuple _ | Value.String _)
  | Syntax.Patt_Tuple _, (Value.Term _ | Value.Closure _ | Value.Handler _ | Value.Tag _ | Value.Ref _ |
                          Value.List _ | Value.String _) ->
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

let multimatch_pattern ps vs =
  Value.get_env >>= fun env ->
  let r = begin try
    let xvs = multicollect_pattern env [] ps vs in
    (* return in decreasing de bruijn order: ready to fold with add_bound *)
    let xvs = List.sort (fun (k,_) (k',_) -> compare k k') xvs in
    let xvs = List.rev_map snd xvs in
    Some xvs
  with Match_fail -> None
  end in
  return r

