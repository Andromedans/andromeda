(** Equality checking and weak-head-normal-forms *)

(** Notation for the monadic bind *)
let (>>=) v f = match v with Some x -> f x | None -> None
let return x = Some x

(** A check is a postponed equality check.
    Pattern matching generates these. *)
type check =
  (* compare terms at a type *)
  | CheckEqual of Pattern.pterm * Tt.term * Tt.ty
  (* compare types in context *)
  | CheckEqualTy of ((Pattern.pty * Tt.ty), (Pattern.pty * Tt.ty)) Tt.abstraction
  (* compare terms for alpha equality *)
  | CheckAlphaEqual of Pattern.pterm * Tt.term

(* counter for debugging depth  *)
let cnt = let msg_cnt = ref (-1) in fun () -> (incr msg_cnt; !msg_cnt)

(** Indicate a mismatch during pattern matching -- only used locally and should
    never escape [verify_match] or [collect_for_XXX] below. *)
exception NoMatch

(** The whnf of a type [t] in environment [env]. *)
let rec whnf_ty env ctx (Tt.Ty t) : Context.t * Tt.ty =
  let ctx, t = whnf env ctx t in
  ctx, Tt.ty t

(** The "weak weak" head-normal form of a term [e] is obtained by ignoring the
    beta hints, sort of. They still get used in beta reductions for comparing
    the typing annotations. So it is a bit unclear what termination properties
    [weak_whnf] might have. There might be a tricky case in which we cycle
    because [beta_reduce] triggers [whnf] which triggers [weak_whnf].
    The important point is that it computes a form of [e] that is suitable
    for pattern-matching of the top-level constructor of [e]. *)
and weak_whnf env ctx ((e', loc) as e) =
  let rec weak ctx ((e', loc) as e) =
    begin match e' with
      | Tt.Spine (e, _, []) -> weak ctx e
      | Tt.Lambda ([], (e, _)) -> weak ctx e
      | Tt.Prod ([], Tt.Ty e) -> weak ctx e
      | Tt.Spine (e, (xts, t), (_::_ as es)) ->
        begin
          let (ctx, ((e',eloc) as e)) = weak ctx e in
          match e' with
          | Tt.Lambda (xus, (e', u)) ->
            begin
              match beta_reduce ~loc:eloc env ctx xus e' u xts t es with
              | None -> (ctx, Tt.mk_spine ~loc e xts t es)
              | Some (ctx, e) -> weak ctx e
            end
          | Tt.Atom _
          | Tt.Constant _
          | Tt.Spine _
          | Tt.Type
          | Tt.Prod _
          | Tt.Eq _
          | Tt.Refl _
          | Tt.Inhab _
          | Tt.Bracket _
          | Tt.Signature _
          | Tt.Structure _
          | Tt.Projection _ ->
             (ctx, Tt.mk_spine ~loc e xts t es)
          | Tt.Bound _ ->
            Error.impossible ~loc "de Bruijn encountered in a spine head in whnf"
        end

      | Tt.Constant _ ->
         (* XXX here we shall use info about primitive operations to normalize some
           of their arguments. *)
         (ctx, e)

      | Tt.Projection (e,xts,p) ->
        begin
          let (ctx, ((e',eloc) as e)) = weak ctx e in
          match e' with
            | Tt.Structure xtes ->
              begin
                match projection_reduce ~loc:eloc env ctx xts p xtes with
                  | None -> (ctx, Tt.mk_projection ~loc e xts p)
                  | Some (ctx,e) -> weak ctx e
              end
            | Tt.Atom _
            | Tt.Constant _
            | Tt.Lambda _
            | Tt.Spine _
            | Tt.Type
            | Tt.Prod _
            | Tt.Eq _
            | Tt.Refl _
            | Tt.Inhab _
            | Tt.Bracket _
            | Tt.Signature _
            | Tt.Projection _ ->
               (ctx, Tt.mk_projection ~loc e xts p)
            | Tt.Bound _ ->
              Error.impossible ~loc "de Bruijn encountered in a projection head in whnf"
        end

      | Tt.Lambda (_ :: _, _)
      | Tt.Prod (_ :: _, _)
      | Tt.Atom _
      | Tt.Type
      | Tt.Eq _
      | Tt.Refl _
      | Tt.Inhab _
      | Tt.Bracket _
      | Tt.Signature _
      | Tt.Structure _ -> (ctx, e)
      | Tt.Bound _ ->
          Error.impossible ~loc "de Bruijn encountered in weak_whnf"
    end
  in
  weak ctx e

(** The whnf of term [e] in environment [env], assuming [e] has a type.
    Here we use available beta hints. *)
and whnf env ctx e =
  let i = cnt () in
  let xs = Environment.used_names env in
  Print.debug "(%i computing whnf of@ %t@ " i (Tt.print_term xs e);
  let ctx, e = weak_whnf env ctx e in
  let rec apply_beta = function
    | [] -> ctx, e
    | ((ctxh, (xts, (p, e'))) as h) :: hs ->
      Print.debug "collecting for beta@ %t@ from@ %t"
        (Pattern.print_beta_hint [] h) (Tt.print_term [] e) ;
      (* XXX Here a failed join need not be fatal, we could catch and continue
         with the remaining hints *)
      let ctx = Context.join ctxh ctx in
      (* Here we use beta hints. First we match [p] against [e]. *)
      begin try
          (* XXX collect_* will return contexts *)
        let (pvars, checks, extras) = collect_for_beta env ctx p e in
        (* we have a match, still need to verify validity of match *)
        Print.debug
          "Found a match of pattern@ %t@ against@ %t@, checking its \
           validity…"
          (Pattern.print_beta_hint xs h)
          (Tt.print_term xs e) ;
        begin match verify_match ~spawn:false env ctx xts pvars checks with
        | None ->
          Print.debug "validity check failed";
          apply_beta hs (* not valid, try other hints *)
        | Some (ctx, es) ->
          (* success *)
          let e' = Tt.instantiate es e' in
          let e' = List.fold_left
              (fun e ((yvs,w),es) -> Tt.mk_spine ~loc:(snd e) e yvs w es) e' extras in
          Print.debug "beta hint@ %t@ matches@ %t,@ we get@ %t"
            (Pattern.print_beta_hint xs h)
            (Tt.print_term xs e)
            (Tt.print_term xs e') ;
          whnf env ctx e'
        end
      with NoMatch -> apply_beta hs (* did not match, try other hints *)
      end
  in
  if !Config.ignore_hints then ctx, e
  else begin
    let key = Pattern.term_key e in
    Print.debug "trying beta hints for@ %t" (Tt.print_term xs e);
    let ctx, e = apply_beta (Environment.beta_hints key env) in
    Print.debug "%i found whnf@ %t )" i (Tt.print_term xs e);
    (ctx, e)
  end

(** Beta reduction of [Lambda (xus, (e, u))] applied to arguments [es],
    where [(yvs, t)] is the typing annotation for the application.
    Returns the resulting expression. *)
and beta_reduce ~loc env ctx xus e u yvs t es =
  let rec split xuvs es' xus yvs es =
    match xus, yvs, es with
    | ([], _, _) | (_, [], []) -> xuvs, es', xus, yvs, es
    | (x,u)::xus, (_,v)::yvs, e::es -> split (xuvs @ [(x,(u,v))]) (e::es') xus yvs es
    | (_, [], _::_) | (_, _::_, []) ->
      Error.impossible ~loc "Equal.beta_reduce encountered an invalid spine"
  in
  let xuvs, es', xus, yvs, es = split [] [] xus yvs es in

  (* [xuvs] is a list of triples [(x,u,v)] ready to be plugged into [equal_abstraction] *)
  (* [es'] is the list of arguments that we are plugging in (reverse order from [es]) *)
  (* [xus] is the list of leftover abstraction arguments *)
  (* [yvs, es] is the list of leftover arguments *)
  (* XXX: optimization -- use the fact that one or both of [xus] and [yevs, es] are empty. *)
  let u' = Tt.mk_prod_ty ~loc xus u
  and t' = Tt.mk_prod_ty ~loc yvs t in
  match equal_abstracted_ty env ctx xuvs u' t' with
  | None -> None (* The types did not match. *)
  | Some ctx -> (* Types match -- we can reduce *)
     let xus, (e, u) = Tt.instantiate_ty_abstraction Tt.instantiate_term_ty es' (xus, (e, u))
     and yvs, t = Tt.instantiate_ty_abstraction Tt.instantiate_ty es' (yvs, t) in
     let e = Tt.mk_lambda ~loc xus e u in
     let e = Tt.mk_spine ~loc e yvs t es in
     Some (ctx, e)

(** Reduction of [{xtes}.p] at type [{xts}] *)
and projection_reduce ~loc env ctx xts p xtes =
  equal_signature ~loc env ctx xts (List.map (fun (l,x,t,_) -> l,x,t) xtes) >>= fun ctx ->
  let te = Tt.field_value ~loc xtes p in
  Some (ctx,te)

(** Let [xuus] be the list [(x1,(u1,u1')); ...; (xn,(un,un'))] where
    [ui]  is well-formed in the context [x1:u1 , ..., x{i-1}:u{i-1} ] and
    [ui'] is well-formed in the context [x1:u1', ..., x{i-1}:u{i-1}'] and
    [v]  is well-formed in the context [x1:u1, ..., xn:un] and
    [v'] is well-formed in the context [x1:u1',..., xn:un'].
    We verify that the [ui] are equal to [ui'] and that [v] is equal to [v]. *)
and equal_abstracted_ty env ctx (xuus : (Name.ident * (Pattern.pty * Tt.ty)) list) v v' =
  (* As we descend into the contexts we carry around a list of variables
     [ys] with which we unabstract the bound variables. *)
  let rec eq env ctx ys =
    function
     | [] ->
        let v = Tt.unabstract_ty ys v
        and v' = Tt.unabstract_ty ys v' in
        equal_ty env ctx v v'
     | (x,(u,u'))::xuus ->
        let u  = Tt.unabstract_ty ys u
        and u' = Tt.unabstract_ty ys u' in
        equal_ty env ctx u u' >>= fun ctx ->
        let ju = Judgement.mk_ty ctx u in
        let y, env = Environment.add_fresh ~loc:Location.unknown env x ju in
        eq env ctx (ys @ [y]) xuus (* XXX optimize list append *)
  in
  eq env ctx [] xuus

(** Compare two types *)
and equal_ty env ctx (Tt.Ty t1) (Tt.Ty t2) = equal env ctx t1 t2 Tt.typ

and equal env ctx ((_,loc1) as e1) ((_,loc2) as e2) t =
  let xs = Environment.used_names env in
  let i = cnt () in
  Print.debug "(%i checking equality of@ %t@ and@ %t@ at type@ %t" i
    (Tt.print_term xs e1) (Tt.print_term xs e2) (Tt.print_ty xs t);
  let r =
  if Tt.alpha_equal e1 e2 then return ctx else
    begin (* type-directed phase *)
      let (ctx, ((Tt.Ty (t',_)) as t)) = whnf_ty env ctx t in
      match t' with

        | Tt.Structure _
        | Tt.Lambda _
        | Tt.Refl _
        | Tt.Inhab _
        | Tt.Type ->
           (* It may seem odd that a lambda abstraction or a refl is a type,
              but not impossible in the presence of crazy hints. *)
           equal_hints env ctx e1 e2 t

        | Tt.Atom _
        | Tt.Constant _
        | Tt.Projection _
        | Tt.Spine _ ->
           (** Here we apply eta hints. *)
           begin
             let rec fold = function

              | [] ->
                (* no hints apply, proceed with applying general hints *)
                equal_hints env ctx e1 e2 t

              |  ((ctxh, (xts, (pt, k1, k2))) as h) :: hs ->
                let debug_i = cnt () in
                Print.debug "(%d collecting for eta %t" debug_i (Pattern.print_eta_hint [] h);
                (* XXX Here a failed join need not be fatal, we could catch and continue
                   with the remaining hints *)
                let ctx = Context.join ctxh ctx in
                begin match collect_for_eta env ctx (pt, k1, k2) (t, e1, e2) with
                  | None -> 
                     Print.debug "collecting for eta failed early %d)" debug_i;
                     fold hs (* no match, try other hints *)
                  | Some (pvars, checks) ->
                    (* check validity of the match *)
                    begin match verify_match ~spawn:true env ctx xts pvars checks with
                      | Some (ctx, _) ->
                         Print.debug "collecting for eta worked %d)" debug_i;
                         return ctx (* success - notice how we throw away the witness of success *)
                      | None ->
                         Print.debug "collecting for eta failed late %d)" debug_i;
                         fold hs (* no match on this hint, try the rest *)
                    end
                end

            in let key = Pattern.ty_key t in
            fold (if !Config.ignore_hints then []
                  else (Environment.eta_hints key env))
          end

        | Tt.Prod (xus, u) ->
            let rec fold env ys es =
              begin function
              | (x, ((Tt.Ty (_, loc)) as v)) :: xvs ->
                  let v = Tt.unabstract_ty ys v in
                  let jv = Judgement.mk_ty ctx v in
                  let y, env =  Environment.add_fresh ~loc env x jv in
                  let e = Tt.mk_atom ~loc y in
                  fold env (y :: ys) (e :: es) xvs
              | [] ->
                  let es = List.rev es in
                  let v = Tt.unabstract_ty ys u
                  and e1 = Tt.mk_spine ~loc:loc1 e1 xus u es
                  and e2 = Tt.mk_spine ~loc:loc2 e2 xus u es
                  in equal env ctx e1 e2 v
              end
            in fold env [] [] xus

        | Tt.Eq _ -> return ctx (** Strict equality *)

        | Tt.Bracket _ -> return ctx (** Strict bracket types *)

        | Tt.Signature xts ->
          (* vs contains all the previous projections of e1 *)
          let rec fold ctx vs = function
            | [] -> return ctx
            | (l,x,t)::rem ->
              let t = Tt.instantiate_ty vs t in
              let e1 = Tt.mk_projection ~loc:loc1 e1 xts l in
              let e2 = Tt.mk_projection ~loc:loc2 e2 xts l in
              equal env ctx e1 e2 t >>= fun ctx ->
              fold ctx (e1::vs) rem
            in
          fold ctx [] xts

        | Tt.Bound _ -> Error.impossible ~loc:loc1 "deBruijn encountered in equal"

    end in
  Print.debug "%i equality check %s)" i
    (match r with | None -> "failed" | Some _ -> "succeeded") ;
  r

(* Compare expressions at a given type [t] using general hints. *)
and equal_hints env ctx e1 e2 t =
  (* First we normalize the expressions *)
  (* XXX can break general hints on functions. First note that when we get
     here, eta expansion has already been applied. Now h : f ≡ λx.x will fail
     because the rhs [(λx.x) y] reduces to [y] but [f y] is stuck and h won't
     apply anymore *)
  let (ctx, ((e1',loc1) as e1)) = whnf env ctx e1 in
  let (ctx, ((e2',loc2) as e2)) = whnf env ctx e2 in
  (* short-circuit alpha equality *)
  if Tt.alpha_equal e1 e2 then
    return ctx
  else
    (* try general hints *)
    let r =
      begin
        let key = Pattern.general_key e1 e2 t in
        Print.debug "Looking for a general hint with keys: %t" (Pattern.print_general_key key);

        let rec fold = function
          | ((ctxh, (xts, (pt, pe1, pe2))) as h) :: hs ->
             (* XXX Here a failed join need not be fatal, we could catch and continue
                with the remaining hints *)
             let ctx = Context.join ctx ctxh in
             Print.debug "trying general hint@ %t" (Pattern.print_hint [] h);
             begin match collect_for_hint env ctx (pt, pe1, pe2) (t, e1, e2) with
             | None -> fold hs
             | Some (pvars, checks) ->
                (* check validity of the match *)
                Print.debug "verifying match";
                begin match verify_match ~spawn:false env ctx xts pvars checks with
                | Some (ctx, _) -> Some ctx (* success - notice how we throw away the witness of success *)
                | None -> fold hs
                end
             end
          | [] -> None
        in
        fold (if !Config.ignore_hints then [] else Environment.general_hints key env)
      end in
    begin match r with
    | None ->
       (* proceed with comparing the weak head normal forms *)
       equal_whnf env ctx e1 e2
    | Some ctx -> return ctx
    end

(* Compare normalized expressions. The assumption is that they both
   have a common type. *)
and equal_whnf env ctx (e1',loc1) (e2',loc2) =
  (* compare reduced expressions *)
  Print.debug "equal_whnf of %t and %t" (Tt.print_term [] (e1',loc1)) (Tt.print_term [] (e2',loc2)) ;
  match e1', e2' with

  | Tt.Atom x, Tt.Atom y ->
     if Name.eq_atom x y then return ctx
     else None

  | Tt.Bound _, _ | _, Tt.Bound _ ->
     Error.impossible ~loc:loc1 "deBruijn encountered in equal_whnf"

  | Tt.Constant (x1, es1), Tt.Constant (x2, es2) ->
     if not @@ Name.eq_ident x1 x2
     then None
     else
       let yts, _ =
         begin match Environment.lookup_constant x1 env with
         | Some ytsu -> ytsu
         | None -> Error.impossible "primitive application equality, unknown primitive operation %t" (Name.print_ident x1)
         end in
       let rec fold ctx es' yts es1 es2 =
         match yts, es1, es2 with
         | [], [], [] -> return ctx

         | (y,(reduce,t))::yts, e1::es1, e2::es2 ->
            if reduce
            then equal_whnf env ctx e1 e2
            else equal env ctx e1 e2 (Tt.instantiate_ty es' t)
              >>= fun ctx ->
              fold ctx (e1 :: es') yts es1 es2

         | _, _, _ ->
            Error.impossible ~loc:loc1 "primitive application equality (%d, %d, %d)"
              (List.length yts)
              (List.length es1)
              (List.length es2)
       in
       fold ctx [] yts es1 es2

  | Tt.Lambda (xus, (e1, t1)), Tt.Lambda (xvs, (e2, t2)) ->
     let rec zip ys env = function
       | (x, u) :: xus, (_, u') :: xvs ->
          let u  = Tt.unabstract_ty ys u
          and u' = Tt.unabstract_ty ys u' in
          equal_ty env ctx u u' >>= fun ctx ->
          let ju = Judgement.mk_ty ctx u in
          let y, env = Environment.add_fresh ~loc:Location.unknown env x ju in
          zip (ys @ [y]) env (xus, xvs) (* XXX optimize list append *)

       | ([] as xus), xvs | xus, ([] as xvs) ->
          let t1' = Tt.mk_prod_ty ~loc:Location.unknown xus t1
          and t2' = Tt.mk_prod_ty ~loc:Location.unknown xvs t2 in
          let t1' = Tt.unabstract_ty ys t1'
          and t2' = Tt.unabstract_ty ys t2' in
          equal_ty env ctx t1' t2' >>= fun ctx ->
          let e1 = Tt.mk_lambda ~loc:(snd e1) xus e1 t1
          and e2 = Tt.mk_lambda ~loc:(snd e2) xvs e2 t2 in
          let e1 = Tt.unabstract ys e1
          and e2 = Tt.unabstract ys e2 in
          equal env ctx e1 e2 t1'
     in
     zip [] env (xus, xvs)

  | Tt.Spine (e1, xts1, es1), Tt.Spine (e2, xts2, es2) ->
     equal_spine ~loc:loc1 env ctx e1 (xts1, es1) e2 (xts2, es2)

  | Tt.Type, Tt.Type -> return ctx

  | Tt.Prod (xus, t1), Tt.Prod (xvs, t2) ->
     let rec zip xuvs = function
       | (x, u) :: xus, (_, v) :: xvs ->
          zip ((x, (u, v)) :: xuvs) (xus, xvs)
       | ([] as xus), xvs | xus, ([] as xvs) ->
          let xuvs = List.rev xuvs in
          let t1 = Tt.mk_prod_ty ~loc:loc1 xus t1
          and t2 = Tt.mk_prod_ty ~loc:loc2 xvs t2 in
          equal_abstracted_ty env ctx xuvs t1 t2
     in
     zip [] (xus, xvs)

  | Tt.Eq (u, d1, d2), Tt.Eq (u', d1', d2') ->
     equal_ty env ctx u u' >>= fun ctx ->
     equal env ctx d1 d1' u >>= fun ctx ->
     equal env ctx d2 d2' u

  | Tt.Refl (u, d), Tt.Refl (u', d') ->
     equal_ty env ctx u u' >>= fun ctx ->
     equal env ctx d d' u

  | Tt.Inhab t, Tt.Inhab t' ->
     equal_ty env ctx t t'

  | Tt.Bracket t1, Tt.Bracket t2 ->
     equal_ty env ctx t1 t2

  | Tt.Signature xts1, Tt.Signature xts2 -> equal_signature ~loc:loc1 env ctx xts1 xts2

  | Tt.Structure xtes1, Tt.Structure xtes2 ->
    let xts1 = List.map (fun (l,x,t,_) -> l,x,t) xtes1 in
    let xts2 = List.map (fun (l,x,t,_) -> l,x,t) xtes2 in
    equal_signature ~loc:loc1 env ctx xts1 xts2 >>= fun ctx ->
    equal_module ~loc:loc1 env ctx xtes1 xtes2

  | Tt.Projection (te1,xts1,p1), Tt.Projection (te2,xts2,p2) ->
    if Name.eq_ident p1 p2
    then
      equal_signature ~loc:loc1 env ctx xts1 xts2 >>= fun ctx ->
      equal_whnf env ctx te1 te2
    else None

  | (Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Spine _ |
     Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _ |
     Tt.Signature _ | Tt.Structure _ | Tt.Projection _), _ ->
     None

and equal_spine ~loc env ctx e1 a1 e2 a2 =
  (* We deal with nested spines. They are nested in an inconvenient way so
     we first get them the way we need them. *)
  let rec collect_spines ab abs n ((e',_) as e) =
    match e' with
    | Tt.Spine (e, xts, es) -> collect_spines (xts,es) (ab :: abs) (n + List.length es) e
    | _ -> e, ab, abs, n
  in
  let h1, a1, as1, n1 = collect_spines a1 [] (List.length (snd a1)) e1
  and h2, a2, as2, n2 = collect_spines a2 [] (List.length (snd a2)) e2 in
  if not (n1 = n2)
  then None
  else return ctx >>=
  begin
    let rec fold es1 es2 ((xts1, u1), ds1) as1 ((xts2, u2), ds2) as2 ctx =

      match (xts1, ds1), (xts2, ds2) with

      | ([], []), (xts2, ds2) ->
         begin
           match as1 with
           | [] ->
              assert (as2 = []) ;
              assert (xts2 = []) ;
              assert (ds2 = []) ;
              let u1 = Tt.instantiate_ty es1 u1
              and u2 = Tt.instantiate_ty es2 u2 in
              equal_ty env ctx u1 u2 >>=
              (* Compare the spine heads. We postpone doing so until
                 we have checked that they have the same type, which
                 we did because we compared [u1] and [u2] as well as
                 the types of all the binders we encountered *)
              fun ctx -> equal_whnf env ctx h1 h2

           | ((xts1, v1), ds1) :: as1 ->
              let u1 = Tt.instantiate_ty es1 u1 in
              let u1' = Tt.mk_prod_ty ~loc xts1 v1 in
              equal_ty env ctx u1 u1' >>=
              (* we may flatten spines and proceed with equality check *)
              fold [] es2 ((xts1, v1), ds1) as1 ((xts2, u2), ds2) as2
              (* else we may not flatten the spine *)
              (* XXX think what to do here really *)
         end

      | (((_::_) as xts1), ((_::_) as ds1)), ([], []) ->
        begin
          match as2 with
          | [] -> assert false

          | ((xts2, v2), ds2) :: as2 ->
            let u2 = Tt.instantiate_ty es2 u2 in
            let u2' = Tt.mk_prod_ty ~loc xts2 v2 in
              equal_ty env ctx u2 u2' >>=
              (* we may flatten spines and proceed with equality check *)
              fold es1 [] ((xts1, u1), ds1) as1 ((xts2, v2), ds2) as2
              (* else we may not flatten the spine *)
              (* XXX think what to do here really *)
        end

      | ((x1,t1) :: xts1, e1::ds1), ((x2,t2)::xts2, e2::ds2) ->
        let t1 = Tt.instantiate_ty es1 t1
        and t2 = Tt.instantiate_ty es2 t2 in
        equal_ty env ctx t1 t2 >>=
        fun ctx -> equal env ctx e1 e2 t1 >>=
        begin
          let es1 = e1 :: es1
          and es2 = e2 :: es2
          in
          fold es1 es2 ((xts1, u1), ds1) as1 ((xts2, u2), ds2) as2
        end

      | ([], _::_), _ | (_::_, []), _ | _, ([], _::_) | _, (_::_, []) ->
        Error.impossible "Equal.equal_spine encountered an invalid spine"
    in
    fold [] [] a1 as1 a2 as2
  end

and equal_signature ~loc env ctx xts1 xts2 =
  let rec fold env ctx ys xts1 xts2 = match xts1, xts2 with
    | [], [] -> Some (Context.abstract ~loc ctx ys) (* do we need to abstract here? *)
    | (l1,x,t1)::xts1, (l2,_,t2)::xts2 ->
      if Name.eq_ident l1 l2
      then
        let t1 = Tt.unabstract_ty ys t1 in
        let t2 = Tt.unabstract_ty ys t2 in
        equal_ty env ctx t1 t2 >>= fun ctx ->
        let jx = Judgement.mk_ty ctx t1 in
        let y, env = Environment.add_fresh ~loc env x jx in
        fold env ctx (y::ys) xts1 xts2
      else None
    | _::_,[] | [],_::_ -> None
    in
  fold env ctx [] xts1 xts2

(** this function assumes that the derived signatures have already been checked equal label to label *)
and equal_module ~loc env ctx xtes1 xtes2 =
  let rec fold ctx vs xtes1 xtes2 = match xtes1, xtes2 with
    | [], [] ->
      Some ctx
    | (l1,x,t1,te1)::xts1, (l2,_,t2,te2)::xts2 ->
      if Name.eq_ident l1 l2
      then
        let ty = Tt.instantiate_ty vs t1 in (* here we need to know that ctx |- instantiate t1 == instantiate t2. Is this true? *)
        let te1 = Tt.instantiate vs te1 in
        let te2 = Tt.instantiate vs te2 in
        equal env ctx te1 te2 ty >>= fun ctx ->
        fold ctx (te1::vs) xts1 xts2
      else None
    | _::_,[] | [],_::_ -> None
    in
  fold ctx [] xtes1 xtes2

(** [pattern_collect env p ?t e] matches pattern [p] against term [e]
    of possibly given type [t].

    It outputs two lists [pvars] and [checks].
    The list [pvars] maps pattern variables to the terms they were
    matched against. The list [checks] contains equalities which
    must be verified before the match is considered valid.
    It raises [NoMatch] if there is a mismatch. *)

and pattern_collect env ctx p ?at_ty e =
    Print.debug "collecting %t" (Tt.print_term [] e) ;
    let (ctx, e) = whnf env ctx e in
    pattern_collect_whnf env ctx p ?at_ty e

(* Collect from [e] assuming it is in whnf. *)
and pattern_collect_whnf env ctx p ?at_ty ((e', loc) as e) =
  Print.debug "collecting pattern %t from whnf %t"
    (Pattern.print_pattern [] ([],p)) (Tt.print_term [] e) ;
  match p with

  | Pattern.Atom x' ->
    begin match e' with
    | Tt.Atom x -> if Name.eq_atom x' x then [], [] else raise NoMatch
    | _ -> raise NoMatch
    end

  | Pattern.PVar k ->
    begin match at_ty with
    | Some t -> [(k, (e, t))], []
    | None ->
      (** We only get here if the caller of [pattern_collect] does not provide
          [t] _and_ we hit a variable as top-most pattern. This can happen
          if someone installed a useless beta hint, for example. So maybe
          a warning is warnted at this point. *)
      raise NoMatch
    end

  | Pattern.Constant (x, pes) ->
    begin match e' with
      | Tt.Constant (y, es) -> collect_primapp ~loc env ctx x pes y es
      | _ -> raise NoMatch
    end

  | Pattern.Spine (pe, (xts, u), pes) ->
    begin match e' with
      | Tt.Spine (e, (yus, v), es) ->
        let pvars, checks, extras = pattern_collect_spine ~loc env ctx (pe, (xts, u), pes) (e, (yus, v), es) in
        begin match extras with
        | _::_ ->
          Print.debug "found unexpected trailing arguments at %t"
            (Tt.print_term (Environment.used_names env) (e', loc));
          raise NoMatch
        | [] ->
          Print.debug "no trailing arguments for %t"
            (Tt.print_term (Environment.used_names env) (e', loc));
          pvars, checks
        end
      | _ -> raise NoMatch
    end

  | Pattern.Eq (pt, pe1, pe2) ->
    begin match e' with
      | Tt.Eq (t, e1, e2) ->
        let pvars_t, checks_t = pattern_collect_ty env ctx pt t
        and pvars_e1, checks_e1 = pattern_collect env ctx pe1 ~at_ty:t e1
        and pvars_e2, checks_e2 = pattern_collect env ctx pe2 ~at_ty:t e2
        in pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2
      | _ -> raise NoMatch
    end

  | Pattern.Refl (pt, pe) ->
    begin match e' with
      | Tt.Refl (t, e) ->
        let pvars_t, checks_t = pattern_collect_ty env ctx pt t
        and pvars_e, checks_e = pattern_collect env ctx pe ~at_ty:t e
        in pvars_t @ pvars_e, checks_t @ checks_e
      | _ -> raise NoMatch
    end

  | Pattern.Bracket pt ->
    begin match e' with
      | Tt.Bracket t -> pattern_collect_ty env ctx pt t
      | _ -> raise NoMatch
    end

  | Pattern.Term (e',t') ->
    begin match at_ty with
      | Some t -> [], [CheckEqualTy ([], (t', t)); CheckEqual (e', e, t)]
      | None ->
        (** It is unsafe to compare [e'] and [e] for equality when
            the type of [e] is not given. However, it is safe to
            compare for alpha equality. And in fact we need this
            to be able to rewrite constants (names). *)
        [], [CheckAlphaEqual (e', e)]
    end

(* Collect from a type. *)
and pattern_collect_ty env ctx (Pattern.Ty p) (Tt.Ty e) =
  pattern_collect env ctx p ~at_ty:Tt.typ e

(* Collect pattern variables from a spine, and return trailing arguments.
   Also account for nested spines. *)
and pattern_collect_spine ~loc env ctx (pe, xtsu, pes) (e, yvsw, es) =

  (* We deal with nested spines. They are nested in an inconvenient way so
     we first get them the way we need them. *)
  let rec collect_spines_terms ab abs n ((e',_) as e) =
    match e' with
    | Tt.Spine (e, xtsu, es) -> collect_spines_terms (xtsu,es) (ab :: abs) (n + List.length es) e
    | _ -> e, ab, abs, n (* [e] should be a [Tt.Constant]. *)
  in

  let rec collect_spines_patterns ab abs n pe =
    match pe with
    | Pattern.Spine (pe, xtsu, pes) -> collect_spines_patterns (xtsu, pes) (ab :: abs) (n + List.length pes) pe
    | _ -> pe, ab, abs, n (* [e] should be a [Pattern.Constant] *)
  in

  let ph, pargs, pargss, n1 = collect_spines_patterns (xtsu, pes) [] (List.length pes) pe
  and  h,  args,  argss, n2 = collect_spines_terms    (yvsw, es)  [] (List.length es)  e
  in

  (* If the pattern spine is longer than the arguments spine the match will fail. *)
  if n1 > n2 then raise NoMatch ;

  (* match the heads *)
  (* The type comes from the *term* not the pattern and thus doesn't contain pvars *)
  let pvars_head, checks_head =
    begin
      let t = (let ((yvs, w), _) = args in Tt.mk_prod_ty ~loc yvs w) in
      pattern_collect_whnf env ctx ph ~at_ty:t h
    end
  in

  let rec fold xtvs es' ((xts, u), pes) pargss ((yvs, w), es) argss =
    match xts, pes, yvs, es with

    | (x,t)::xts, pe::pes, (y,v)::yvs, e::es ->
      Print.debug "collect spine (1): collect arg@ %t at %t@ from@ %t at %t"
        (Pattern.print_pattern [] ([], pe)) (Tt.print_ty [] t)
        (Tt.print_term [] e) (Tt.print_ty [] v);
      let t = Tt.instantiate_ty es' t
      and v = Tt.instantiate_ty es' v in
      Print.debug "collect spine (2): collect arg@ %t at %t@ from@ %t at %t"
        (Pattern.print_pattern [] ([], pe)) (Tt.print_ty [] t)
        (Tt.print_term [] e) (Tt.print_ty [] v);
      let pvars_e, checks_e = pattern_collect env ctx pe ~at_ty:v e in
      let xtvs = (x,(t,v)) :: xtvs in
      let es' = e :: es' in
      let pvars, checks, extras = fold xtvs es' ((xts, u), pes) pargss ((yvs, w), es) argss in
        pvars_e @ pvars, checks_e @ checks, extras

    | ((_::_) as xts), ((_::_) as pes), [], [] ->
      begin
        match argss with
        | [] -> Error.impossible ~loc "invalid spine in pattern match (1)"
        | ((yvs, w'), es) :: argss ->
          let t1 = Tt.instantiate_ty es' w
          and t2 = Tt.mk_prod_ty ~loc yvs w' in
          match equal_ty env ctx t1 t2 with
          | None -> raise NoMatch
          | Some ctx -> fold xtvs es' ((xts,u), pes) pargss ((yvs, w'), es) argss
      end

    | [], [], _::_, _::_ ->
      begin
        let xtvs = List.rev xtvs in

        let u = Tt.instantiate_ty es' u
        and yvs, w = Tt.instantiate_ty_abstraction Tt.instantiate_ty es' (yvs, w) in
        let w_prod = Tt.mk_prod_ty ~loc yvs w in

        let check_uw = CheckEqualTy (xtvs, (u, w_prod)) in
        match pargss with
        | [] -> [], [check_uw], ((yvs, w), es) :: argss
        | pargs :: pargss ->
          let pvars, checks, extras = fold [] [] pargs pargss ((yvs, w), es) argss in
          pvars, check_uw :: checks, extras
      end

    | [], [], [], [] ->
      begin
        let xtvs = List.rev xtvs in
        (* the return types may still contain variables bound to the arguments
           of the spine; instantiate them. *)
        let w = Tt.instantiate_ty es' w in
        let u = Tt.instantiate_ty es' u in

        let check_uw = CheckEqualTy (xtvs, (u, w)) in
          match pargss, argss with
            | [], argss -> [], [check_uw], argss
            | pargs::pargss, args::argss ->
              let pvars, checks, extras = fold [] [] pargs pargss args argss in
                pvars, check_uw :: checks, extras
            | _::_, [] -> Error.impossible ~loc "invalid spine in pattern match (2)"
      end

    | [], _::_, _, _ | _::_, [], _, _ ->
      Error.impossible ~loc "invalid spine pattern encountered in pattern collection"
    | _, _, [], _::_ | _, _, _::_, [] ->
      Error.impossible ~loc "invalid spine encountered in pattern collection"
  in
  let pvars, checks, extras = fold [] [] pargs pargss args argss in
    pvars_head @ pvars, checks_head @ checks, extras

(** Collect values of pattern variables by matching a beta
    pattern [bp] against whnf expression [e]. Also return the residual
    equations that remain to be checked, and the unused
    arguments. *)
and collect_for_beta env ctx bp (e',loc) =
  match bp, e' with

  | Pattern.BetaAtom x, Tt.Atom y ->
    if Name.eq_atom x y
    then [], [], []
    else raise NoMatch

  | Pattern.BetaAtom x, Tt.Spine (e, yts, es) ->
    let rec fold args (e',_) yts es =
      match e' with
        | Tt.Atom y ->
          if Name.eq_atom x y
          then (yts, es) :: args
          else raise NoMatch
        | Tt.Spine (e', yts', es') ->
          fold ((yts, es) :: args) e' yts' es'
        | _ -> raise NoMatch    (* XXX remove catch-all *)
    in
    let extras = fold [] e yts es in
    ([], [], extras)

  | Pattern.BetaConstant (x, pes), Tt.Spine (e, yts, es) ->
Print.debug "collect_beta for %t" (Name.print_ident x) ;
    let rec fold extras (e',_) yts es =
      match e' with
        | Tt.Constant (y, es') ->
           let extras = (yts, es) :: extras in
           let extras = List.rev extras in
           y, es', extras
        | Tt.Spine (e', yts', es') -> fold ((yts, es) :: extras) e' yts' es'
        | _ -> raise NoMatch
    in
    let y, es, extras = fold [] e yts es in
    let pvars, checks = collect_primapp ~loc env ctx x pes y es in
Print.debug "collect_beta for %t WORKED" (Name.print_ident x) ;
    (pvars, checks, extras)

  | Pattern.BetaConstant (x, pes), Tt.Constant (y, es) ->
     let pvars, checks = collect_primapp ~loc env ctx x pes y es in
     (pvars, checks, [])

  | Pattern.BetaSpine (pe, xts, pes), Tt.Spine (e, yts, es) ->
    pattern_collect_spine ~loc env ctx (pe, xts, pes) (e, yts, es)

  | (Pattern.BetaAtom _ | Pattern.BetaSpine _ | Pattern.BetaConstant _), _ ->
    raise NoMatch

and collect_primapp ~loc env ctx x pes y es =
  if not (Name.eq_ident x y)
  then raise NoMatch
  else begin
    let yts, _ =
      begin match Environment.lookup_constant x env with
            | Some ytsu -> ytsu
            | None -> Error.impossible ~loc "unknown operation %t in pattern_collect" (Name.print_ident x)
      end in
    let rec fold es' yts pes es =
      match yts, pes, es with
      | [], [], [] -> [], []

      | (y,(reducing,t))::yts, pe::pes, e::es ->
         let pvars_e, checks_e =
            begin
              let t = Tt.instantiate_ty es' t in
              if reducing
              then pattern_collect_whnf env ctx pe ~at_ty:t e
              else pattern_collect      env ctx pe ~at_ty:t e
            end in
         let pvars, checks = fold (e::es') yts pes es in
         pvars_e @ pvars, checks_e @ checks

      | _, _, _ ->
         Error.impossible ~loc "malformed primitive applications in pattern_collect"
    in
    fold [] yts pes es
  end

(** Similar to [collect_for_beta] except ctx targeted at extracting
  values of pattern variable and residual equations in eta hints,
  where we compare a type and two terms. *)
and collect_for_eta env ctx (pt, k1, k2) (t, e1, e2) =
  try
    let pvars_t,  checks_t  = pattern_collect_ty env ctx pt t in
      Some ((k1,(e1,t)) :: (k2,(e2,t)) :: pvars_t, checks_t)
  with NoMatch -> None

and collect_for_hint env ctx (pt, pe1, pe2) (t, e1, e2) =
  try
    let pvars_t, checks_t = pattern_collect_ty env ctx pt t
    and pvars_e1, checks_e1 = pattern_collect env ctx pe1 ~at_ty:t e1
    and pvars_e2, checks_e2 = pattern_collect env ctx pe2 ~at_ty:t e2 in
    Some (pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2)
  with NoMatch -> None

and collect_for_inhabit env ctx pt t =
  try
    let pvars_t, checks_t = pattern_collect_ty env ctx pt t in
    Some (pvars_t, checks_t)
  with NoMatch -> None

(** Verify that the results of a [collect_XXX] constitute a valid
    match, i.e., that the pattern variables have been matched with
    values that have the correct types.

    The [spawn] flag tells whether we should spawn an equality
    check when we encounter an unmatched pattern variable.
    For an eta hint [spawn] would be true, but for a beta hint
    it would be false. It would be interesting to consider what
    happens if [spawn] is set to true in beta hints. Do we cycle?
*)
and verify_match ~spawn env ctx xts pvars checks =
  let debug_i = cnt () in
  Print.debug "(%d verify_match" debug_i ;

  (* Silly auxiliary function. *)
  let rec lookup x = function
    | [] -> None
    | (y,z)::lst -> if x = y then Some z else lookup x lst
  in

  (* Create a substitution from an association list mapping
     pattern variables to their values. As you go, check that
     the types of pattern variables are equal to the ones found
     by the pattern match. If an unbound variable is encountered
     try to inhabit it when [spawn] is [true]. Return a list of
     inhabitation problems that need to be checked later for this
     match to be successful. *)
  let rec subst_of_pvars env ctx pvars k xts es inhs =
    match xts with
    | [] -> ctx, es, inhs
    | (_,t) :: xts ->
      begin match lookup k pvars with

        | Some (e,t') ->
          (* Pattern variable [k] is matched to [e] of type [t'].
             We need to verify that [t] and [t'] are equal. *)
          let t = Tt.instantiate_ty es t in
          Print.debug "matching: compare %t and %t (es %d)" (Tt.print_ty [] t) (Tt.print_ty [] t') (List.length es);
          begin match equal_ty env ctx t t' with
          | None -> raise NoMatch
          | Some ctx -> subst_of_pvars env ctx pvars (k-1) xts (e :: es) inhs
          end

        | None ->
          if not spawn
          then raise NoMatch (* we are not supposed to instantiate missing variables *)
          else begin
            (* Try to inhabit the type [t]. Actually, we first calculate the
               only possible candidate, and redo the check later when we actually
               know that the pattern match will succeed. *)
            let t = Tt.instantiate_ty es t in
            Print.debug "matching: trying to inhabit@ %t" (Tt.print_ty [] t) ;
            match inhabit ~subgoals:false env ctx t with
              | None -> raise NoMatch (* didn't work *)
              | Some (ctx, e) -> subst_of_pvars env ctx pvars (k-1) xts (e :: es) ((env,t) :: inhs)
          end
      end
  in

  try
    (* Make a substitution from the collected [pvars] *)
    let ctx, es, inhs = subst_of_pvars env ctx pvars (List.length xts - 1) xts [] [] in
    Print.debug "built substitution %d" debug_i;
    (* Perform the equality checks to validate the match *)
    let ctx =
      List.fold_left
        (fun ctx -> function
           | CheckEqual (e1, e2, t) ->
              let e1 = Tt.instantiate es e1 in
              Print.debug "CheckEqual at@ %t@ %t@ %t"
                (Tt.print_ty (Environment.used_names env) t)
                (Tt.print_term (Environment.used_names env) e1)
                (Tt.print_term (Environment.used_names env) e2);
              begin match equal env ctx e1 e2 t with
              | Some ctx -> ctx
              | None -> raise NoMatch
              end

           | CheckEqualTy (xuvs, (t1, t2)) ->

              (* All de Bruijn indices refer to pvars from the point of view of
                 the body, we therefore must not instantiate with
                 [Tt.instantiate_abstraction] which expects them to be relative to
                 the current abstraction *)
              let xuvs = List.map (fun (x, (pt, t)) -> x, (Tt.instantiate_ty es pt, t)) xuvs in
              let t1', t2' =  Tt.instantiate_ty es t1, t2 in

              Print.debug "%d es: %t" debug_i
                (Print.sequence (Tt.print_term ~max_level:0 []) "; " es);

              Print.debug "%d instantiated pattern return type@ %t@ as@ %t" debug_i
                (Tt.print_ty [] t1)
                (Tt.print_ty [] t1') ;

              Print.debug "%d instantiated rhs-term return type@ %t@ as@ %t" debug_i
                (Tt.print_ty [] t2)
                (Tt.print_ty [] t2') ;

              Print.debug "%d CheckEqualTy@ %t@ %t" debug_i
                (Tt.print_ty [] t1')
                (Tt.print_ty [] t2');
              begin match equal_abstracted_ty env ctx xuvs t1' t2' with
              | Some ctx -> ctx
              | None -> raise NoMatch
              end

           | CheckAlphaEqual (e1, e2) ->
              let e1 = Tt.instantiate es e1 in
              if not (Tt.alpha_equal e1 e2) then raise NoMatch else ctx) ctx
        checks in
    (* Perform delayed inhabitation goals *)
    (* XXX why is it safe to delay these? *)
    let ctx = List.fold_left
        (fun ctx (env, t) ->
           match inhabit ~subgoals:true env ctx t with
           | None -> raise NoMatch
           | Some (ctx, _) -> ctx) ctx
      inhs in
    (* match succeeded *)
    Print.debug "succeeded %d)" debug_i ;
    Some (ctx, es)
  with NoMatch ->
    Print.debug "failed %d)" debug_i ;
    None (* matching failed *)

and as_bracket env (ctx, t) =
  let (ctxt, Tt.Ty (t', loc)) = whnf_ty env ctx t in
  match t' with
  | Tt.Bracket t -> ctxt, t
  | _ -> Error.typing ~loc "[] has a bracket type and not %t" (Tt.print_ty (Environment.used_names env) t)

(** Strip brackets from a given type. *)
and strip_bracket env ctx t =
  let (ctx, Tt.Ty (t', loc)) = whnf_ty env ctx t in
  match t' with
  | Tt.Bracket t -> strip_bracket env ctx t
  | _ ->  ctx, t (* XXX or should be return the whnf t? *)

(** Try to inhabit the given type [t], which must be proof-irrelevant.
    If [subgoals] is [true] then recursively resolve goals, otherwise
    just return the only possible inhabitant of [t]. *)
and inhabit ~subgoals env ctx t =
  let (ctx, (Tt.Ty (t', loc) as t)) = whnf_ty env ctx t in
  inhabit_whnf ~subgoals env ctx t

and inhabit_whnf ~subgoals env ctx ((Tt.Ty (t', loc)) as t) =
  Print.debug "trying to inhabit (subgoals = %b) whnf@ %t"
    subgoals (Tt.print_ty [] t);
  match t' with

    | Tt.Prod (xts', t') ->
      let rec fold env ys = function
        | [] ->
          let t' = Tt.unabstract_ty ys t' in
          begin match inhabit ~subgoals env ctx t' with
            | None -> None
            | Some (ctx, e) ->
              let e = Tt.abstract ys e in
              let e = Tt.mk_lambda ~loc xts' e t' in
              let ctx = Context.abstract ~loc ctx ys in
              Some (ctx, e)
          end
        | (x,t)::xts ->
          let t = Tt.unabstract_ty ys t in
          let jt = Judgement.mk_ty ctx t in
          let y, env = Environment.add_fresh ~loc env x jt in
          fold env (y :: ys) xts
      in
        fold env [] xts'

    | Tt.Eq (t, e1, e2) ->
       if not subgoals
       then
         (* Do not create new subgoals, just return the only
            possible candidate for inhabitation. *)
         let e = Tt.mk_refl ~loc t e1 in
         return (ctx, e)
       else
         equal env ctx e1 e2 t >>= fun ctx ->
           let e = Tt.mk_refl ~loc t e1 in
           return (ctx, e)

    | Tt.Bracket t ->
       let jt = Judgement.mk_ty ctx t in
       inhabit_bracket ~subgoals ~loc env jt

    | Tt.Atom _
    | Tt.Constant _
    | Tt.Spine _
    | Tt.Bound _
    | Tt.Lambda _
    | Tt.Refl _
    | Tt.Inhab _
    | Tt.Signature _
    | Tt.Structure _
    | Tt.Projection _
    | Tt.Type -> None

and inhabit_bracket ~subgoals ~loc env (ctx, t_inhabit) =
  if not subgoals then
    Some (ctx, Tt.mk_inhab ~loc t_inhabit)
  else
    (* apply inhabit hints *)
    let ctx, t = strip_bracket env ctx t_inhabit in
    let key = Pattern.ty_key t in
    let rec fold = function
      | [] -> None
      | ((ctxh, (xts, pt)) as h) :: hs ->
         Print.debug "attempting to inhabit@ %t using@ %t"
                     (Tt.print_ty [] t) (Pattern.print_inhabit_hint [] h) ;
         (* XXX Here a failed join need not be fatal, we could catch and continue
            with the remaining hints *)
         let ctx = Context.join ctx ctxh in
         begin match collect_for_inhabit env ctx pt t with
         | None -> fold hs
         | Some (pvars, checks) ->
            (* check validity of the match *)
            begin match verify_match ~spawn:true env ctx xts pvars checks with
                  | Some (ctx, _) -> Some (ctx, Tt.mk_inhab ~loc t_inhabit)
                  | None -> fold hs
            end
         end
    in fold (Environment.inhabit_hints key env)

let as_atom env (ctx, e', t)  =
  let ctx, ((e', loc) as e) = whnf env ctx e' in
  match e' with
  | Tt.Atom x -> (ctx, x, t)
  | Tt.Prod _ | Tt.Type | Tt.Eq _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ ->
    Error.runtime ~loc "this expression should be an atom"

let rec deep_prod env ctx t f =
  let ctx, (Tt.Ty (t', loc)) = whnf_ty env ctx t in
  match t' with

  | Tt.Prod ([], _) -> Error.impossible ~loc "empty product encountered in deep_prod"

  | Tt.Prod ((_ :: _) as xus, w) ->

     let rec fold env ys zvs =
       begin match zvs with
       | [] ->
          let w = Tt.unabstract_ty ys w in
          let ctx, (zvs, w) = deep_prod env ctx w f in
          let (zvs, w) = Tt.abstract_ty_abstraction Tt.abstract_ty ys (zvs, w) in
          let ctx = Context.abstract ~loc ctx ys in
          (ctx, (xus @ zvs, w))

       | (z,v) :: zvs ->
          let v = Tt.unabstract_ty ys v in
          let jv = Judgement.mk_ty ctx v in
          let y, env = Environment.add_fresh ~loc env z jv in
          fold env (y :: ys) zvs
       end in

     fold env [] xus

  | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Eq _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ ->
     let ctx, t = f env ctx (Tt.ty (t', loc)) in
     (ctx, ([], t))

let as_prod env (ctx, t) = deep_prod env ctx t (fun env ctx x -> (ctx, x))

let as_eq env (ctx, ((Tt.Ty (_, loc)) as t)) =
  let ctx, Tt.Ty (t', _) =  whnf_ty env ctx t in
  match t' with

  | Tt.Eq (t, e1, e2) -> (ctx, t, e1, e2)

  | Tt.Prod _ | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ ->
     Error.typing ~loc
       "this expression should be an equality type, found@ %t"
       (Tt.print_ty [] t)


let as_universal_eq env (ctx, ((Tt.Ty (_, loc)) as t)) =
  let ctx, (xus, (Tt.Ty (t', loc) as t)) = as_prod env (ctx, t) in
  match t' with

  | Tt.Eq (t, e1, e2) ->
     (ctx, (xus, (t, e1, e2)))

  | Tt.Prod _ -> Error.impossible ~loc "product encountered in as_universal_eq"

  | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ ->
     Error.typing ~loc
       "the type of this expression should be a universally quantified equality, found@ %t"
       (Tt.print_ty [] t)

let as_universal_bracket env (ctx, ((Tt.Ty (_, loc)) as t)) =
  deep_prod
    env ctx t
    (fun env ctx ((Tt.Ty (t', loc)) as t) ->
     match t' with

     | Tt.Bracket t -> strip_bracket env ctx t

     | Tt.Prod _ -> Error.impossible ~loc "product encountered in as_universal_bracket"

     | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
     | Tt.Spine _ | Tt.Refl _ | Tt.Inhab _
     | Tt.Signature _ | Tt.Structure _ | Tt.Projection _
     | Tt.Eq _ -> ctx, t)


let as_signature env (ctx, t) =
  let (ctxt, Tt.Ty (t', loc)) = whnf_ty env ctx t in
  match t' with
    | Tt.Signature xts -> ctxt, xts
    | _ -> Error.typing ~loc
      "this expressing should be a signature, found@ %t"
      (Tt.print_ty [] t)

let rec snf env ctx t =
  let ctx, ((t',loc) as t) = whnf env ctx t in
  match t' with
    | Tt.Type | Tt.Atom _ -> ctx, t

    | Tt.Bound _ -> Error.impossible ~loc "de Bruijn encountered in snf"

    | Tt.Constant (c,es) ->
      let rec fold ctx es = function
        | [] ->
          let es = List.rev es in
          ctx, Tt.mk_constant ~loc c es
        | e::rem ->
          let ctx, e = snf env ctx e in
          fold ctx (e::es) rem
      in
      fold ctx [] es

    | Tt.Lambda (abs,(te,ty)) ->
      let rec fold env ctx ys abs = function
        | [] ->
          let abs = List.rev abs in
          let ty = Tt.unabstract_ty ys ty in
          let te = Tt.unabstract ys te in
          let ctx, ty = snf_ty env ctx ty in
          let ctx, te = snf env ctx te in
          let ty = Tt.abstract_ty ys ty in
          let te = Tt.abstract ys te in
          let ctx = Context.abstract ~loc ctx ys in
          ctx, Tt.mk_lambda ~loc abs te ty
        | (x,t)::rem ->
          let t = Tt.unabstract_ty ys t in
          let ctx, t = snf_ty env ctx t in
          let jx = Judgement.mk_ty ctx t in
          let y, env = Environment.add_fresh ~loc env x jx in
          let t = Tt.abstract_ty ys t in
          fold env ctx (y::ys) ((x,t)::abs) rem
      in
      fold env ctx [] [] abs

    | Tt.Spine (lhs,(abs,out),rhs) ->
      let ctx, lhs = snf env ctx lhs in
      let rec fold_rhs ctx rhs = function
        | [] ->
          let rhs = List.rev rhs in
          ctx, rhs
        | e::rem ->
          let ctx, e = snf env ctx e in
          fold_rhs ctx (e::rhs) rem
      in
      let ctx, rhs = fold_rhs ctx [] rhs in
      let rec fold env ctx ys abs = function
        | [] ->
          let abs = List.rev abs in
          let out = Tt.unabstract_ty ys out in
          let ctx, out = snf_ty env ctx out in
          let out = Tt.abstract_ty ys out in
          let ctx = Context.abstract ~loc ctx ys in
          ctx, Tt.mk_spine ~loc lhs abs out rhs
        | (x,t)::rem ->
          let t = Tt.unabstract_ty ys t in
          let ctx, t = snf_ty env ctx t in
          let jx = Judgement.mk_ty ctx t in
          let y, env = Environment.add_fresh ~loc env x jx in
          let t = Tt.unabstract_ty ys t in
          fold env ctx (y::ys) ((x,t)::abs) rem
      in
      fold env ctx [] [] abs

    | Tt.Prod (abs,out) ->
      let rec fold env ctx ys abs = function
        | [] ->
          let abs = List.rev abs in
          let out = Tt.unabstract_ty ys out in
          let ctx, out = snf_ty env ctx out in
          let out = Tt.abstract_ty ys out in
          let ctx = Context.abstract ~loc ctx ys in
          ctx, Tt.mk_prod ~loc abs out
        | (x,t)::rem ->
          let t = Tt.unabstract_ty ys t in
          let ctx, t = snf_ty env ctx t in
          let jx = Judgement.mk_ty ctx t in
          let y, env = Environment.add_fresh ~loc env x jx in
          let t = Tt.abstract_ty ys t in
          fold env ctx (y::ys) ((x,t)::abs) rem
      in
      fold env ctx [] [] abs

    | Tt.Eq (t,e1,e2) ->
      let ctx, t = snf_ty env ctx t in
      let ctx, e1 = snf env ctx e1 in
      let ctx, e2 = snf env ctx e2 in
      ctx, Tt.mk_eq ~loc t e1 e2

    | Tt.Refl (t,e) ->
      let ctx, t = snf_ty env ctx t in
      let ctx, e = snf env ctx e in
      ctx, Tt.mk_refl ~loc t e

    | Tt.Inhab t ->
      let ctx, t = snf_ty env ctx t in
      ctx, Tt.mk_inhab ~loc t

    | Tt.Bracket t ->
      let ctx, t = snf_ty env ctx t in
      ctx, Tt.mk_bracket ~loc t

    | Tt.Signature xts ->
      let rec fold env ctx ys xts = function
        | [] ->
          let xts = List.rev xts in
          let ctx = Context.abstract ~loc ctx ys in
          ctx, Tt.mk_signature ~loc xts
        | (l,x,t)::rem ->
          let t = Tt.unabstract_ty ys t in
          let ctx, t = snf_ty env ctx t in
          let jx = Judgement.mk_ty ctx t in
          let y, env = Environment.add_fresh ~loc env x jx in
          let t = Tt.abstract_ty ys t in
          fold env ctx (y::ys) ((l,x,t)::xts) rem
      in
      fold env ctx [] [] xts

    | Tt.Structure xes ->
      let rec fold env ctx ys xes = function
        | [] ->
          let xes = List.rev xes in
          let ctx = Context.abstract ~loc ctx ys in
          ctx, Tt.mk_structure ~loc xes
        | (l,x,t,e)::rem ->
          let t = Tt.unabstract_ty ys t in
          let e = Tt.unabstract ys e in
          let ctx, t = snf_ty env ctx t in
          let ctx, e = snf env ctx e in
          let jx = Judgement.mk_ty ctx t in
          let y, env = Environment.add_fresh ~loc env x jx in
          let t = Tt.abstract_ty ys t in
          let e = Tt.abstract ys e in
          (* XXX should we add a beta hint x --> e here? *)
          fold env ctx (y::ys) ((l,x,t,e)::xes) rem
      in
      fold env ctx [] [] xes

    | Tt.Projection (e,xts,l) ->
      let ctx, e = snf env ctx e in
      let rec fold env ctx ys xts = function
        | [] ->
          let xts = List.rev xts in
          let ctx = Context.abstract ~loc ctx ys in
          ctx, Tt.mk_projection ~loc e xts l
        | (l,x,t)::rem ->
          let t = Tt.unabstract_ty ys t in
          let ctx, t = snf_ty env ctx t in
          let jx = Judgement.mk_ty ctx t in
          let y, env = Environment.add_fresh ~loc env x jx in
          let t = Tt.abstract_ty ys t in
          fold env ctx (y::ys) ((l,x,t)::xts) rem
      in
      fold env ctx [] [] xts

and snf_ty env ctx (Tt.Ty t) =
  let ctx, t = snf env ctx t in
  ctx, Tt.ty t

