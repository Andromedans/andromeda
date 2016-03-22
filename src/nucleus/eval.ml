(** Evaluation of computations *)

(** Notation for the monadic bind *)
let (>>=) = Runtime.bind

(** A filter that verifies the result is a term. *)
let as_term ~loc v =
  let e = Runtime.as_term ~loc v in
    Runtime.return e

(** Returns the atom with its natural type in [ctx] *)
let as_atom ~loc v =
  as_term ~loc v >>= fun (Jdg.Term (ctx,e,t) as j) ->
  match e.Tt.term with
    | Tt.Atom x ->
      begin match Context.lookup_ty x ctx with
        | Some t -> Runtime.return (ctx,x,t)
        | None ->
          Runtime.lookup_penv >>= fun penv ->
          Error.impossible ~loc "got an atom judgement %t but the atom is not in the context" (Jdg.print_term ~penv j)
      end
    | _ -> Runtime.print_term >>= fun print_term ->
      Error.runtime ~loc "expected an atom but got %t" (print_term e)

let as_handler ~loc v =
  let e = Runtime.as_handler ~loc v in
  Runtime.return e

let as_ref ~loc v =
  let e = Runtime.as_ref ~loc v in
  Runtime.return e

let as_list ~loc v =
  let lst = Predefined.as_list ~loc v in
  Runtime.return lst

let as_ident ~loc v =
  let s = Runtime.as_ident ~loc v in
  Runtime.return s

(** Evaluate a computation -- infer mode. *)
let rec infer {Location.thing=c'; loc} =
  match c' with
    | Syntax.Bound i ->
       Runtime.lookup_bound ~loc i

    | Syntax.Type ->
       let e = Tt.mk_type ~loc in
       let t = Tt.mk_type_ty ~loc in
       let et = Jdg.mk_term Context.empty e t in
       Runtime.return_term et

    | Syntax.Function (x, c) ->
       let f v =
         Runtime.add_bound x v
           (infer c)
       in
       Runtime.return_closure f

    | Syntax.Constructor (t, cs) ->
       let rec fold vs = function
         | [] ->
            let vs = List.rev vs in
            let v = Runtime.mk_tag t vs in
            Runtime.return v
         | c :: cs ->
            infer c >>= fun v ->
            fold (v :: vs) cs
       in
       fold [] cs

    | Syntax.Tuple cs ->
      let rec fold vs = function
        | [] -> Runtime.return (Runtime.mk_tuple (List.rev vs))
        | c :: cs -> (infer c >>= fun v -> fold (v :: vs) cs)
      in
      fold [] cs

    | Syntax.Handler {Syntax.handler_val; handler_ops; handler_finally} ->
        let handler_val =
          begin match handler_val with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~loc handler_val infer v
            in
            Some f
          end
        and handler_ops = Name.IdentMap.mapi (fun op cases ->
            let f {Runtime.args=vs;checking} =
              match_op_cases ~loc op cases vs checking
            in
            f)
          handler_ops
        and handler_finally =
          begin match handler_finally with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~loc handler_finally infer v
            in
            Some f
          end
        in
        Runtime.return_handler handler_val handler_ops handler_finally

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op vs
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.With (c1, c2) ->
     infer c1 >>= as_handler ~loc >>= fun h ->
     Runtime.handle_comp h (infer c2)

  | Syntax.Let (xcs, c) ->
     let_bind xcs (infer c)

  | Syntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (infer c)

  | Syntax.Now (x,c1,c2) ->
    infer c1 >>= fun v ->
    Runtime.now ~loc x v (infer c2)

  | Syntax.Ref c ->
     infer c >>= fun v ->
     Runtime.mk_ref v

  | Syntax.Lookup c ->
     infer c >>= as_ref ~loc >>= fun x ->
     Runtime.lookup_ref x

  | Syntax.Update (c1, c2) ->
     infer c1 >>= as_ref ~loc >>= fun x ->
     infer c2 >>= fun v ->
     Runtime.update_ref x v >>= fun () ->
     Runtime.return_unit

  | Syntax.Sequence (c1, c2) ->
     infer c1 >>= fun v ->
     sequence ~loc v >>= fun () ->
     infer c2

  | Syntax.Assume ((x, t), c) ->
     check_ty t >>= fun t ->
     Runtime.add_free ~loc x t (fun _ _ ->
       infer c)

  | Syntax.Where (c1, c2, c3) ->
    infer c2 >>= as_atom ~loc >>= fun (_, a, _) ->
    infer c1 >>= fun v1 ->
    as_term ~loc v1 >>= fun (Jdg.Term (ctx, e1, t1)) ->
    Runtime.lookup_penv >>= fun penv ->
    begin match Context.lookup_ty a ctx with
    | None -> infer c3 >>=
       as_term ~loc:(c3.Location.loc) >>= fun _ ->
       Runtime.return v1
    | Some ta ->
       check c3 (Jdg.mk_ty ctx ta) >>= fun (ctx, e2) ->
       let ctx_s = Context.substitute ~penv ~loc a (ctx,e2,ta) in
       let te_s = Tt.substitute [a] [e2] e1 in
       let ty_s = Tt.substitute_ty [a] [e2] t1 in
       let j_s = Jdg.mk_term ctx_s te_s ty_s in
       Runtime.return_term j_s
    end

  | Syntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases infer

  | Syntax.External s ->
     begin match External.lookup s with
       | None -> Error.runtime ~loc "unknown external %s" s
       | Some v -> v loc
     end

  | Syntax.Ascribe (c1, c2) ->
     check_ty c2 >>= fun (Jdg.Ty (_,t') as t) ->
     check c1 t >>= fun (ctx, e) ->
     let j = Jdg.mk_term ctx e t' in
     Runtime.return_term j

  | Syntax.Constant x ->
    Runtime.lookup_constant ~loc x >>= fun t ->
    let e = Tt.mk_constant ~loc x in
    let eu = Jdg.mk_term Context.empty e t in
    Runtime.return_term eu

  | Syntax.Lambda (x,u,c) ->
     infer_lambda ~loc x u c

  | Syntax.Apply (c1, c2) ->
    infer c1 >>= begin function
      | Runtime.Term j ->
        apply ~loc j c2
      | Runtime.Closure f ->
        infer c2 >>= fun v ->
        Runtime.apply_closure f v
      | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
        Runtime.Ref _ | Runtime.String _ | Runtime.Ident _ as h ->
        Error.runtime ~loc "cannot apply %s" (Runtime.name_of h)
    end

  | Syntax.Prod (x,u,c) ->
    infer_prod ~loc x u c

  | Syntax.Eq (c1, c2) ->
     infer c1 >>= as_term ~loc:(c1.Location.loc) >>= fun (Jdg.Term (ctx, e1, t1')) ->
     let t1 = Jdg.mk_ty ctx t1' in
     check c2 t1 >>= fun (ctx, e2) ->
     let eq = Tt.mk_eq ~loc t1' e1 e2 in
     let typ = Tt.mk_type_ty ~loc in
     let j = Jdg.mk_term ctx eq typ in
     Runtime.return_term j

  | Syntax.Refl c ->
     infer c >>= as_term ~loc:(c.Location.loc) >>= fun (Jdg.Term (ctxe, e, t)) ->
     let e' = Tt.mk_refl ~loc t e
     and t' = Tt.mk_eq_ty ~loc t e e in
     let et' = Jdg.mk_term ctxe e' t' in
     Runtime.return_term et'

  | Syntax.Signature (s,lxcs) ->
    let rec align res def lxcs = match def, lxcs with
      | [], [] -> List.rev res
      | lxt::def, [] -> align ((lxt,None)::res) def []
      | [], (l,_,_)::_ -> Error.runtime ~loc "Field %t did not appear in %t." (Name.print_ident l) (Name.print_ident s)
      | ((l,_,_) as lxt)::def, (l',_,_)::_ when (not (Name.eq_ident l l')) ->
        align ((lxt,None)::res) def lxcs
      | lxt::def, (_,x,c)::lxcs ->
        align ((lxt,Some (x,c))::res) def lxcs
    in
    (* [vs] are the constraints,
       [es] instantiate types,
       [ys:ts] are assumed for unconstrained fields *)
    let rec fold ctx vs es ys ts = function
      | [] ->
        let vs = List.rev vs in
        Runtime.lookup_penv >>= fun penv ->
        let ctx = List.fold_left2 (Context.abstract ~penv ~loc) ctx ys ts in
        let s = Tt.mk_signature_ty ~loc (s,vs) in
        let j = Jdg.term_of_ty (Jdg.mk_ty ctx s) in
        Runtime.return_term j
      | ((_,_,t),Some (x,mc))::rem ->
        let t = Tt.instantiate_ty es t in
        let jt = Jdg.mk_ty ctx t in
        begin match mc with
          | Some c ->
            check c jt >>= fun (ctx,e) ->
            let je = Jdg.mk_term ctx e t in
            let e_abs = Tt.abstract ys e in
            Runtime.add_bound x (Runtime.mk_term je)
            (fold ctx ((Tt.Constrained e_abs) :: vs) (e::es) ys ts rem)
          | None ->
            Runtime.add_abstracting ~loc x jt (fun ctx y ->
            let ey = Tt.mk_atom ~loc y in
            fold ctx ((Tt.Unconstrained x)::vs) (ey::es) (y::ys) (t::ts) rem)
        end
      | ((_,x,t),None)::rem ->
        let t = Tt.instantiate_ty es t in
        let jt = Jdg.mk_ty ctx t in
        Runtime.add_abstracting ~loc ~bind:false x jt (fun ctx y ->
        let ey = Tt.mk_atom ~loc y in
        fold ctx ((Tt.Unconstrained x)::vs) (ey::es) (y::ys) (t::ts) rem)
    in
    Runtime.lookup_signature ~loc s >>= fun def ->
    fold Context.empty [] [] [] [] (align [] def lxcs)

  | Syntax.Structure lxcs ->
    (* In infer mode the structure must be fully specified. *)
    let rec prefold ls xcs = function
      | [] -> List.rev ls, List.rev xcs
      | (l,x,Some c)::rem -> prefold (l::ls) ((x,c)::xcs) rem
      | (l,_,None)::_ ->
        Error.runtime ~loc "Field %t must be specified in infer mode." (Name.print_ident l)
    in
    let ls, xcs = prefold [] [] lxcs in
    Runtime.find_signature ~loc ls >>= fun (s,lxts) ->
    let rec fold ctx shares es xcs lxts =
      match xcs, lxts with
        | [], [] ->
          let es = List.rev es in
          let s = (s,List.rev shares) in
          let str = Tt.mk_structure ~loc s es in
          let t_str = Tt.mk_signature_ty ~loc s in
          let j_str = Jdg.mk_term ctx str t_str in
          Runtime.return_term j_str

        | (x, c) :: lxcs, (_, _, t) :: lxts ->
          let t_inst = Tt.instantiate_ty es t in
          let jty = Jdg.mk_ty ctx t_inst in
          check c jty >>= fun (ctx, e) ->
          Runtime.add_bound x (Runtime.mk_term (Jdg.mk_term ctx e t_inst))
          (fold ctx ((Tt.Unconstrained x)::shares) (e::es) lxcs lxts)

        | _::_, [] -> Error.typing ~loc "this structure has too many fields"
        | [], _::_ -> Error.typing ~loc "this structure has too few fields"
    in
    fold Context.empty [] [] xcs lxts

  | Syntax.Projection (c,p) ->
    infer_projection ~loc c p

  | Syntax.Yield c ->
    infer c >>= fun v ->
    Runtime.continue ~loc v

  | Syntax.Hypotheses ->
     Runtime.lookup_abstracting >>= fun lst ->
     let v = Predefined.mk_list lst in
     Runtime.return v

  | Syntax.Congruence (c1,c2) ->
    infer c1 >>= as_term ~loc >>= fun (Jdg.Term (ctx,e1,t)) ->
    check c2 (Jdg.mk_ty ctx t) >>= fun (ctx,e2) ->
    Equal.congruence ~loc ctx e1 e2 t >>= begin function
      | Some (ctx,hyps) ->
        let eq = Tt.mk_refl ~loc t e1 in
        let eq = Tt.mention_atoms hyps eq in
        let teq = Tt.mk_eq_ty ~loc t e1 e2 in
        let j = Jdg.mk_term ctx eq teq in
        let v = Runtime.mk_term j in
        Runtime.return (Predefined.from_option (Some v))
      | None -> Runtime.return (Predefined.from_option None)
      end

  | Syntax.Extensionality (c1,c2) ->
    infer c1 >>= as_term ~loc >>= fun (Jdg.Term (ctx,e1,t)) ->
    check c2 (Jdg.mk_ty ctx t) >>= fun (ctx,e2) ->
    Equal.extensionality ~loc ctx e1 e2 t >>= begin function
      | Some (ctx,hyps) ->
        let eq = Tt.mk_refl ~loc t e1 in
        let eq = Tt.mention_atoms hyps eq in
        let teq = Tt.mk_eq_ty ~loc t e1 e2 in
        let j = Jdg.mk_term ctx eq teq in
        let v = Runtime.mk_term j in
        Runtime.return (Predefined.from_option (Some v))
      | None -> Runtime.return (Predefined.from_option None)
      end

  | Syntax.Reduction c ->
     infer c >>= as_term ~loc >>= fun (Jdg.Term (ctx, e, t)) ->
     Equal.reduction_step ctx e >>=
       begin function
         | Some ((ctx, e'), hyps) ->
            let eq = Tt.mk_refl ~loc t e in
            let eq = Tt.mention_atoms hyps eq in
            let teq = Tt.mk_eq_ty ~loc t e e' in
            let eqj = Jdg.mk_term ctx eq teq in
            Runtime.return (Predefined.from_option (Some (Runtime.mk_term eqj)))
         | None -> Runtime.return (Predefined.from_option None)
       end

  | Syntax.String s ->
    Runtime.return (Runtime.mk_string s)

  | Syntax.GenSig (c1,c2) ->
    check_ty c1 >>= fun j1 ->
    Equal.as_signature j1 >>= fun ((_,(s,shares)),_) ->
    if List.for_all (function | Tt.Unconstrained _ -> true | Tt.Constrained _ -> false) shares
    then
      infer c2 >>= as_list ~loc >>= fun xes ->
      Runtime.lookup_signature ~loc s >>= fun def ->
      (* [es] instantiate types, [ys] are the previous unconstrained fields *)
      let rec fold ctx vs es ys ts def xes = match def,xes with
        | [], [] ->
          Runtime.lookup_penv >>= fun penv ->
          let vs = List.rev vs
          and ctx = List.fold_left2 (Context.abstract ~penv ~loc) ctx ys ts in
          let e = Tt.mk_signature_ty ~loc (s,vs) in
          let j = Jdg.term_of_ty (Jdg.mk_ty ctx e) in
          Runtime.return_term j
        | (l,_,t)::def, xe::xes ->
          begin match Predefined.as_constrain ~loc xe with
            | Tt.Unconstrained vx ->
              as_atom ~loc vx >>= fun (ctx',y,ty) ->
              let t = Tt.instantiate_ty es t in
              (* TODO use handled equal? *)
              if Tt.alpha_equal_ty t ty
              then
                Runtime.lookup_penv >>= fun penv ->
                let ctx = Context.join ~penv ~loc ctx ctx' in
                let ey = Tt.mk_atom ~loc y in
                let x = Name.ident_of_atom y in
                fold ctx ((Tt.Unconstrained x)::vs) (ey::es) (y::ys) (t::ts) def xes
              else
                Runtime.print_ty >>= fun pty ->
                Error.typing ~loc "bad non-constraint for field %t: types %t and %t do not match"
                  (Name.print_ident l) (pty t) (pty ty)
            | Tt.Constrained ve ->
              as_term ~loc ve >>= fun (Jdg.Term (ctx',e,te)) ->
              let t = Tt.instantiate_ty es t in
              require_equal_ty ~loc (Jdg.mk_ty ctx t) (Jdg.mk_ty ctx' te) >>= begin function
                | Some (ctx,hyps) ->
                  let e = Tt.mention_atoms hyps e in
                  let e_abs = Tt.abstract ys e in
                  fold ctx ((Tt.Constrained e_abs) :: vs) (e::es) ys ts def xes
                | None ->
                  Runtime.print_ty >>= fun pty ->
                  Error.typing ~loc "bad constraint for field %t: types %t and %t do not match"
                    (Name.print_ident l) (pty t) (pty te)
              end
          end
        | _::_,[] -> Error.runtime ~loc "constraints missing"
        | [],_::_ -> Error.runtime ~loc "too many constraints"
      in
      fold Context.empty [] [] [] [] def xes
    else
      Error.runtime ~loc "Cannot add constraints to already constrained signature"

  | Syntax.GenStruct (c1,c2) ->
    check_ty c1 >>= fun (Jdg.Ty (_,target) as jt) ->
    Equal.as_signature jt >>= fun ((ctx,((s,shares) as s_sig)),hyps) ->
    infer c2 >>= as_list ~loc >>= fun vs ->
    Runtime.lookup_signature ~loc s >>= fun lxts ->
    (* [es] instantiate types, [res] is the explicit fields (which instantiate constraints) *)
    let rec fold ctx res es vs s_data = match s_data,vs with
      | [], [] ->
        let res = List.rev res in
        let e = Tt.mk_structure ~loc s_sig res in
        let e = Tt.mention_atoms hyps e in
        let j = Jdg.mk_term ctx e target in
        Runtime.return_term j
      | ((l,_,t),Tt.Unconstrained _)::s_data,v::vs ->
        as_term ~loc v >>= fun (Jdg.Term (ctx',e,te)) ->
        let t = Tt.instantiate_ty es t in
        require_equal_ty ~loc (Jdg.mk_ty ctx t) (Jdg.mk_ty ctx' te) >>= begin function
          | Some (ctx,hyps) ->
            let e = Tt.mention_atoms hyps e in
            fold ctx (e::res) (e::es) vs s_data
          | None ->
            Runtime.print_ty >>= fun pty ->
            Error.typing ~loc "bad field %t: types %t and %t do not match"
              (Name.print_ident l) (pty t) (pty te)
        end
      | ((_,_,t),Tt.Constrained e)::s_data, vs ->
        let e = Tt.instantiate res e in
        fold ctx res (e::es) vs s_data
      | (_,Tt.Unconstrained _)::_,[] ->
        Error.runtime ~loc "too few fields"
      | [], _::_ ->
        Error.runtime ~loc "too many fields"
    in
    fold ctx [] [] vs (List.combine lxts shares)

  | Syntax.GenProj (c1,c2) ->
    infer c2 >>= as_ident ~loc >>= fun l ->
    infer_projection ~loc c1 l

  | Syntax.Occurs (c1,c2) ->
    infer c1 >>= as_atom ~loc >>= fun (_,x,_) ->
    infer c2 >>= as_term ~loc >>= fun (Jdg.Term (ctx,_,_)) ->
    begin match Context.lookup_ty x ctx with
      | Some t ->
        let j = Jdg.term_of_ty (Jdg.mk_ty ctx t) in
        Runtime.return (Predefined.from_option (Some (Runtime.mk_term j)))
      | None ->
        Runtime.return (Predefined.from_option None)
    end

  | Syntax.Context c ->
    infer c >>= as_term ~loc >>= fun (Jdg.Term (ctx,_,_)) ->
    let xts = Context.elements ctx in
    let js = List.map (fun (x,t) ->
      let e = Tt.mk_atom ~loc x in
      let j = Jdg.mk_term ctx e t in
      Runtime.mk_term j) xts in
    Runtime.return (Predefined.mk_list js)

  | Syntax.Ident x ->
    Runtime.return (Runtime.mk_ident x)

and require_equal_ty ~loc (Jdg.Ty (lctx, lte)) (Jdg.Ty (rctx, rte)) =
  Runtime.lookup_penv >>= fun penv ->
  let ctx = Context.join ~penv ~loc lctx rctx in
  Equal.equal_ty ctx lte rte

and check_default ~loc v (Jdg.Ty (_, t_check') as t_check) =
  as_term ~loc v >>= fun (Jdg.Term (ctxe, e, t')) ->
  require_equal_ty ~loc t_check (Jdg.mk_ty ctxe t') >>=
    begin function
      | Some (ctx, hyps) -> Runtime.return (ctx, Tt.mention_atoms hyps e)
      | None ->
         Runtime.print_term >>= fun pte ->
         Runtime.print_ty >>= fun pty ->
         Error.typing ~loc
                      "the expression %t should have type@ %t@ but has type@ %t"
                      (pte e) (pty t_check') (pty t')
    end

and check ({Location.thing=c';loc} as c) (Jdg.Ty (_, t_check') as t_check) =
  match c' with
  | Syntax.Type
  | Syntax.Bound _
  | Syntax.Function _
  | Syntax.Handler _
  | Syntax.External _
  | Syntax.Constructor _
  | Syntax.Tuple _
  | Syntax.Where _
  | Syntax.With _
  | Syntax.Constant _
  | Syntax.Prod _
  | Syntax.Eq _
  | Syntax.Apply _
  | Syntax.Signature _
  | Syntax.Projection _
  | Syntax.Yield _
  | Syntax.Hypotheses
  | Syntax.Congruence _
  | Syntax.Extensionality _
  | Syntax.Reduction _
  | Syntax.Ref _
  | Syntax.Lookup _
  | Syntax.Update _
  | Syntax.String _
  | Syntax.GenSig _
  | Syntax.GenStruct _
  | Syntax.GenProj _
  | Syntax.Occurs _
  | Syntax.Context _
  | Syntax.Ident _ ->
    (** this is the [check-infer] rule, which applies for all term formers "foo"
        that don't have a "check-foo" rule *)

    infer c >>= fun v ->
    check_default ~loc v t_check

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op ~checking:t_check vs >>= fun v ->
          check_default ~loc v t_check
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.Let (xcs, c) ->
     let_bind xcs (check c t_check)

  | Syntax.Sequence (c1,c2) ->
    infer c1 >>= fun v ->
    sequence ~loc v >>= fun () ->
    check c2 t_check

  | Syntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (check c t_check)

  | Syntax.Now (x,c1,c2) ->
    infer c1 >>= fun v ->
    Runtime.now ~loc x v (check c2 t_check)

  | Syntax.Assume ((x, t), c) ->
     check_ty t >>= fun t ->
     Runtime.add_free ~loc x t (fun _ _ ->
     check c t_check)

  | Syntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases (fun c -> check c t_check)

  | Syntax.Ascribe (c1, c2) ->
     check_ty c2 >>= fun (Jdg.Ty (_,t') as t) ->
     require_equal_ty ~loc t_check t >>=
       begin function
         | Some (ctx, hyps) ->
            let jt = Jdg.mk_ty ctx t' in
            check c1 jt >>= fun (ctx,e) ->
            Runtime.return (ctx,Tt.mention_atoms hyps e)
         | None ->
            Runtime.print_ty >>= fun pty ->
            Error.typing ~loc:(c2.Location.loc)
                         "this type should be equal to@ %t"
                         (pty t_check')
       end

  | Syntax.Lambda (x,u,c) ->
    check_lambda ~loc t_check x u c

  | Syntax.Refl c ->
    Equal.as_eq t_check >>= fun ((ctx, t', e1, e2),hyps) ->
    let t = Jdg.mk_ty ctx t' in
    check c t >>= fun (ctx, e) ->
    Equal.equal ctx e e1 t' >>= begin function
      | None ->
        Runtime.print_term >>= fun pte ->
        Error.typing ~loc "failed to check that the term@ %t is equal to@ %t"
                     (pte e) (pte e1)
      | Some (ctx, hyps1) ->
        Equal.equal ctx e e2 t' >>=
          begin function
            | None ->
              Runtime.print_term >>= fun pte ->
              Error.typing ~loc "failed to check that the term@ %t is equal to@ %t"
                           (pte e) (pte e2)
            | Some (ctx, hyps2) ->
              let e = Tt.mk_refl ~loc t' e in
              let e = Tt.mention_atoms hyps e in
              let e = Tt.mention_atoms hyps1 e in
              let e = Tt.mention_atoms hyps2 e in
              Runtime.return (ctx, e)
          end
      end

  | Syntax.Structure lxcs ->
    Equal.as_signature t_check >>= fun ((ctx,((s,shares) as s_sig)),hyps) ->
    Runtime.lookup_signature ~loc s >>= fun s_def ->
    (* Set up to skip fields not mentioned in [lxcs] *)
    let rec align fields s_data = function
      | [] ->
        let rec complete fields = function
          | [] -> List.rev fields
          | ((_,Tt.Constrained _) as data)::s_data ->
             complete ((data,None)::fields) s_data
          | ((l,_,_),Tt.Unconstrained _)::_ ->
             Error.runtime ~loc "Field %t missing" (Name.print_ident l)
        in
        complete fields s_data
      | (l,x,c)::lxcs ->
        let rec find fields = function
          | (((l',_,_),_) as data)::s_data ->
            if Name.eq_ident l l'
            then
              align ((data,Some (x,c))::fields) s_data lxcs
            else
              find ((data,None)::fields) s_data
          | [] -> Error.runtime ~loc "Field %t does not appear in signature %t"
                                (Name.print_ident l) (Name.print_ident s)
        in
        find fields s_data
    in
    (* [res] is only the explicit fields, [es] instantiates the types *)
    let rec fold ctx res es = function
      | [] ->
        let res = List.rev res in
        let e = Tt.mk_structure ~loc s_sig res in
        let e = Tt.mention_atoms hyps e in
        Runtime.return (ctx,e)
      | (((_,_,t),Tt.Constrained e),Some (x,None))::rem ->
        let e = Tt.instantiate res e
        and t = Tt.instantiate_ty es t in
        let j = Jdg.mk_term ctx e t in
        Runtime.add_bound x (Runtime.mk_term j)
        (fold ctx res (e::es) rem)
      | (((_,_,t),Tt.Unconstrained _),Some (x,Some c))::rem ->
        let t = Tt.instantiate_ty es t in
        let jt = Jdg.mk_ty ctx t in
        check c jt >>= fun (ctx,e) ->
        let j = Jdg.mk_term ctx e t in
        Runtime.add_bound x (Runtime.mk_term j)
        (fold ctx (e::res) (e::es) rem)
      | ((_,Tt.Constrained e),None)::rem ->
        let e = Tt.instantiate res e in
        fold ctx res (e::es) rem
      | (((l,_,_),Tt.Unconstrained _),(None | Some (_,None)))::_ ->
        Error.runtime ~loc "Field %t must be specified" (Name.print_ident l)
      | (((l,_,_),Tt.Constrained _),Some (_,Some _))::_ ->
        Error.runtime ~loc "Field %t is constrained and must not be specified" (Name.print_ident l)
    in
    let fields = align [] (List.combine s_def shares) lxcs in
    fold ctx [] [] fields

and infer_lambda ~loc x u c =
  match u with
    | Some u ->
      check_ty u >>= fun (Jdg.Ty (ctxu, (Tt.Ty {Tt.loc=uloc;_} as u)) as ju) ->
      Runtime.add_abstracting ~loc:uloc x ju (fun _ y ->
      infer c >>= as_term ~loc:(c.Location.loc) >>= fun (Jdg.Term (ctxe,e,t)) ->
      Runtime.lookup_penv >>= fun penv ->
      let ctxe = Context.abstract ~penv ~loc ctxe y u in
      let ctx = Context.join ~penv ~loc ctxu ctxe in
      let e = Tt.abstract [y] e in
      let t = Tt.abstract_ty [y] t in
      let lam = Tt.mk_lambda ~loc x u e t
      and prod = Tt.mk_prod_ty ~loc x u t in
      Runtime.return_term (Jdg.mk_term ctx lam prod))
    | None ->
      Error.runtime ~loc "cannot infer the type of %t" (Name.print_ident x)

and infer_prod ~loc x u c =
  check_ty u >>= fun (Jdg.Ty (ctxu,u) as ju) ->
  let Tt.Ty {Tt.loc=uloc;_} = u in
  Runtime.add_abstracting ~loc:uloc x ju (fun _ y ->
  check_ty c >>= fun (Jdg.Ty (ctx,t)) ->
  Runtime.lookup_penv >>= fun penv ->
  let ctx = Context.abstract ~penv ~loc ctx y u in
  let ctx = Context.join ~penv ~loc ctx ctxu in
  let t = Tt.abstract_ty [y] t in
  let prod = Tt.mk_prod ~loc x u t in
  let typ = Tt.mk_type_ty ~loc in
  let j = Jdg.mk_term ctx prod typ in
  Runtime.return_term j)

and check_lambda ~loc t_check x u c : (Context.t * Tt.term) Runtime.comp =
  Equal.as_prod t_check >>= fun ((ctx,((_,a),b)),hypst) ->
  begin match u with
    | Some u ->
      check_ty u >>= fun (Jdg.Ty (_,u) as ju) ->
      require_equal_ty ~loc (Jdg.mk_ty ctx a) ju >>= begin function
        | Some (ctx,hypsu) ->
          Runtime.return (ctx,u,hypsu)
        | None ->
          Runtime.print_ty >>= fun pty ->
          Error.typing ~loc "this annotation has type %t but should have type %t"
            (pty u) (pty a)
      end
    | None ->
      Runtime.return (ctx,a,Name.AtomSet.empty)
  end >>= fun (ctx,u,hypsu) -> (* u a type equal to a under hypsu *)
  Runtime.add_abstracting ~loc x (Jdg.mk_ty ctx u) (fun ctx y ->
  let y' = Tt.mention_atoms hypsu (Tt.mk_atom ~loc y) in (* y' : a *)
  let b = Tt.instantiate_ty [y'] b in
  check c (Jdg.mk_ty ctx b) >>= fun (ctx,e) ->
  Runtime.lookup_penv >>= fun penv ->
  let ctx = Context.abstract ~penv ~loc ctx y u in
  let e = Tt.abstract [y] e in
  let b = Tt.abstract_ty [y] b in
  let lam = Tt.mk_lambda ~loc x u e b in
  (* lam : forall x : u, b
     == forall x : a, b by hypsu
     == check_ty by hypst *)
  let lam = Tt.mention_atoms (Name.AtomSet.union hypst hypsu) lam in
  Runtime.return (ctx,lam))

and apply ~loc (Jdg.Term (_, h, _) as jh) c =
  Equal.as_prod (Jdg.typeof jh) >>= fun ((ctx,((x,a),b)),hyps) ->
  let h = Tt.mention_atoms hyps h in
  check c (Jdg.mk_ty ctx a) >>= fun (ctx,e) ->
  let res = Tt.mk_apply ~loc h x a b e in
  let out = Tt.instantiate_ty [e] b in
  let j = Jdg.mk_term ctx res out in
  Runtime.return_term j

and infer_projection ~loc c p =
  infer c >>= as_term ~loc >>= fun (Jdg.Term (_,te,_) as j) ->
  let jty = Jdg.typeof j in
  Equal.as_signature jty >>= fun ((ctx,s),hyps) ->
  let te = Tt.mention_atoms hyps te in
  Runtime.lookup_signature ~loc (fst s) >>= fun s_def ->
  (if not (List.exists (fun (l,_,_) -> Name.eq_ident p l) s_def)
  then Error.typing ~loc "Cannot project field %t from signature %t: no such field"
                    (Name.print_ident p) (Name.print_ident (fst s)));
  let te,ty = Tt.field_project ~loc s_def s te p in
  let j = Jdg.mk_term ctx te ty in
  Runtime.return_term j

and sequence ~loc v =
  match v with
    | Runtime.Tuple [] -> Runtime.return ()
    | _ ->
      Runtime.print_value >>= fun pval ->
      Print.warning "%t: Sequence:@ The value %t should be ()" (Location.print loc) (pval v);
      Runtime.return ()

and let_bind : 'a. _ -> 'a Runtime.comp -> 'a Runtime.comp = fun xcs cmd ->
  let rec fold xvs = function
    | [] ->
      (* parallel let: only bind at the end *)
      List.fold_left  (fun cmd (x,v) -> Runtime.add_bound x v cmd) cmd xvs
    | (x, c) :: xcs ->
      infer c >>= fun v ->
      fold ((x, v) :: xvs) xcs
    in
  fold [] xcs

and letrec_bind : 'a. _ -> 'a Runtime.comp -> 'a Runtime.comp = fun fxcs ->
  let gs =
    List.map
      (fun (f, x, c) -> (f, (fun v -> Runtime.add_bound x v (infer c))))
      fxcs
  in
  Runtime.add_bound_rec gs

(* [match_cases loc cases eval v] tries for each case in [cases] to match [v]
   and if successful continues on the computation using [eval] with the pattern variables bound. *)
and match_cases : type a. loc:_ -> _ -> (Syntax.comp -> a Runtime.comp) -> _ -> a Runtime.comp
 = fun ~loc cases eval v ->
  let rec fold = function
    | [] ->
      Runtime.print_value >>= fun pval ->
      Error.runtime ~loc "no match found for %t" (pval v)
    | (xs, p, c) :: cases ->
      Matching.match_pattern p v >>= begin function
        | Some vs ->
          let rec fold2 xs vs = match xs, vs with
            | [], [] -> eval c
            | x::xs, v::vs ->
              Runtime.add_bound x v (fold2 xs vs)
            | _::_, [] | [], _::_ -> Error.impossible ~loc "bad match case"
          in
          fold2 (List.rev xs) vs
        | None -> fold cases
      end
  in
  fold cases

and match_op_cases ~loc op cases vs checking =
  let rec fold = function
    | [] ->
      Runtime.operation op ?checking vs >>= fun v ->
      Runtime.continue ~loc v
    | (xs, ps, pt, c) :: cases ->
      Matching.match_op_pattern ps pt vs checking >>= begin function
        | Some vs ->
          let rec fold2 xs vs = match xs, vs with
            | [], [] -> infer c
            | x::xs, v::vs ->
              Runtime.add_bound x v (fold2 xs vs)
            | _::_, [] | [], _::_ -> Error.impossible ~loc "bad multimatch case"
          in
          fold2 (List.rev xs) vs
        | None -> fold cases
      end
  in
  fold cases

and check_ty c : Jdg.ty Runtime.comp =
  check c Jdg.ty_ty >>= fun (ctx, e) ->
  let t = Tt.ty e in
  let j = Jdg.mk_ty ctx t in
  Runtime.return j


(** Move to toplevel monad *)

let comp_value c =
  let r = infer c in
  Runtime.top_handle ~loc:c.Location.loc r

let comp_handle (xs,y,c) =
  Runtime.top_return_closure (fun (vs,checking) ->
      let rec fold2 xs vs = match xs,vs with
        | [], [] ->
           begin match y with
           | Some y ->
              let checking = match checking with
                | Some jt -> Some (Runtime.mk_term (Jdg.term_of_ty jt))
                | None -> None
              in
              let vy = Predefined.from_option checking in
              Runtime.add_bound y vy (infer c)
           | None -> infer c
           end
        | x::xs, v::vs -> Runtime.add_bound x v (fold2 xs vs)
        | [],_::_ | _::_,[] -> Error.impossible ~loc:(c.Location.loc) "bad top handler case"
      in
      fold2 xs vs)

let comp_signature ~loc lxcs =
  let (>>=) = Runtime.bind in
  let rec fold ys yts lxts = function
    | [] ->
       let lxts = List.rev lxts in
       Runtime.return lxts

    | (l,x,c) :: lxcs ->
       check_ty c >>= fun (Jdg.Ty (ctxt,t)) ->
       if not (Context.is_subset ctxt yts)
       then Error.runtime ~loc "signature field %t has unresolved assumptions"
           (Name.print_ident l)
       else begin
         let jt = Jdg.mk_ty ctxt t
         and tabs = Tt.abstract_ty ys t in
         Runtime.add_abstracting ~loc x jt (fun _ y ->
             fold (y::ys) ((y,t)::yts) ((l,x,tabs) :: lxts) lxcs)
       end
  in
  Runtime.top_handle ~loc (fold [] [] [] lxcs)

(** Toplevel commands *)

let (>>=) = Runtime.top_bind
let return = Runtime.top_return

let rec mfold f acc = function
  | [] -> return acc
  | x::rem -> f acc x >>= fun acc ->
     mfold f acc rem

let toplet_bind ~loc ~quiet xcs =
  let rec fold xvs = function
    | [] ->
       (* parallel let: only bind at the end *)
       List.fold_left
         (fun cmd (x,v) ->
            Runtime.add_topbound ~loc x v >>= fun () ->
            if not quiet && not (Name.is_anonymous x)
            then Format.printf "%t is defined.@." (Name.print_ident x) ;
            cmd)
         (return ())
         xvs
    | (x, c) :: xcs ->
       comp_value c >>= fun v ->
       fold ((x, v) :: xvs) xcs
  in
  fold [] xcs

let topletrec_bind ~loc ~quiet fxcs =
  let gs =
    List.map
      (fun (f, x, c) -> (f, (fun v -> Runtime.add_bound x v (infer c))))
      fxcs
  in
  Runtime.add_topbound_rec ~loc gs >>= fun () ->
  if not quiet then
    List.iter (fun (f, _, _) ->
        if not (Name.is_anonymous f) then
          Format.printf "%t is defined.@." (Name.print_ident f)) fxcs ;
  return ()

let add_def = function
  | Syntax.ML_Alias _ -> return ()
  | Syntax.ML_Sum lst ->
    mfold (fun () (cstr, _) -> Runtime.add_forbidden cstr) () lst

let rec toplevel ~quiet {Location.thing=c;loc} =
  match c with

  | Syntax.DefMLType lst ->
    mfold (fun names (t,(_,def)) -> add_def def >>= fun () -> return (t::names)) [] lst >>= fun names ->
    let names = List.rev names in
    (if not quiet then Format.printf "Type%s %t declared.@." (match names with [] -> "" | _ -> "s") (Print.sequence Name.print_ident " " names));
    return ()

  | Syntax.DefMLTypeRec lst ->
    mfold (fun names (t,(_,def)) -> add_def def >>= fun () -> return (t::names)) [] lst >>= fun names ->
    let names = List.rev names in
    (if not quiet then Format.printf "Type%s %t declared.@." (match names with [] -> "" | _ -> "s") (Print.sequence Name.print_ident " " names));
    return ()

  | Syntax.DeclOperation (x, k) ->
     Runtime.add_forbidden x >>= fun () ->
     if not quiet then Format.printf "Operation %t is declared.@." (Name.print_ident x) ;
     return ()

  | Syntax.DeclConstants (xs, c) ->
     Runtime.top_handle ~loc:(c.Location.loc) (check_ty c) >>= fun (Jdg.Ty (ctxt, t)) ->
     if Context.is_empty ctxt
     then
       let rec fold = function
         | [] -> return ()
         | x :: xs ->
            Runtime.add_constant ~loc x t >>= fun () ->
            (if not quiet then Format.printf "Constant %t is declared.@." (Name.print_ident x) ;
             fold xs)
       in
       fold xs
     else
       Error.typing "Constants may not depend on free variables" ~loc:(c.Location.loc)

  | Syntax.DeclSignature (s, lxcs) ->
     comp_signature ~loc lxcs >>= fun lxts ->
     Runtime.add_signature ~loc s lxts  >>= fun () ->
     (if not quiet then Format.printf "Signature %t is declared.@." (Name.print_ident s) ;
      return ())

  | Syntax.TopHandle lst ->
     mfold (fun () (op, xc) ->
         comp_handle xc >>= fun f ->
         Runtime.add_handle op f) () lst

  | Syntax.TopLet xcs ->
     toplet_bind ~loc ~quiet xcs

  | Syntax.TopLetRec fxcs ->
     topletrec_bind ~loc ~quiet fxcs

  | Syntax.TopDynamic (x,c) ->
     comp_value c >>= fun v ->
     Runtime.add_dynamic ~loc x v

  | Syntax.TopNow (x,c) ->
     comp_value c >>= fun v ->
     Runtime.top_now ~loc x v

  | Syntax.TopDo c ->
     comp_value c >>= fun v ->
     Runtime.top_print_value >>= fun print_value ->
     (if not quiet then Format.printf "%t@." (print_value v) ;
      return ())

  | Syntax.TopFail c ->
     Runtime.catch (fun () -> comp_value (Lazy.force c)) >>= begin function
     | Error.Err err ->
        (if not quiet then Format.printf "The command failed with error:\n%t@." (Error.print err));
        return ()
     | Error.OK v ->
        Runtime.top_print_value >>= fun pval ->
        Error.runtime ~loc "The command has not failed: got %t." (pval v)
     end

  | Syntax.Included lst ->
    mfold (fun () (fn, cmds) ->
        (if not quiet then Format.printf "#including %s@." fn);
        mfold (fun () cmd -> toplevel ~quiet:true cmd) () cmds >>= fun () ->
        (if not quiet then Format.printf "#processed %s@." fn);
        return ())
      () lst

  | Syntax.Verbosity i -> Config.verbosity := i; return ()

  | Syntax.Quit ->
     exit 0

