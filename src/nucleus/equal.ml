(** Equality checking and weak-head-normal-forms *)

(** Notation for the monads bind *)

module Monad = struct
  type state = Name.AtomSet.t
  type 'a t =
    { k : 'r. ('a -> state -> 'r Value.result) -> state -> 'r Value.result }

  let return x =
    { k = fun c s -> c x s }

  let (>>=) (m:'a t) (f:'a -> 'b t) : 'b t =
    { k = fun c s -> m.k (fun x s -> (f x).k c s) s }

  let lift m =
    { k = fun c s -> Value.bind m (fun x -> c x s) }

  let modify f =
    { k = fun c s -> c () (f s) }

  let add_hyps hyps = modify (Name.AtomSet.union hyps)

  (** Hypotheses [ys] are replaced by terms [es],
      so mentions of [ys] are replaced by mentions of the assumptions in [es] *)
  let abstract_hyps ys es =
    if ys = [] && es = []
    then return ()
    else
      modify (fun hyps ->
        List.fold_left2 (fun hyps y e ->
            if Name.AtomSet.mem y hyps
            then
              let hyps = Name.AtomSet.remove y hyps in
              let hyps_e = Tt.assumptions_term e in
              let hyps = Name.AtomSet.union hyps hyps_e in
              hyps
            else hyps)
          hyps ys es)

  let run m =
    m.k (fun x s -> Value.return (x,s)) (Name.AtomSet.empty)
end

module Opt = struct
  type state = Monad.state

  type 'a opt =
    { k : 'r. ('a -> state -> 'r Value.result) -> (state -> 'r Value.result) -> state -> 'r Value.result }

  let return x =
    { k = fun sk _ s -> sk x s }

  let (>?=) m f =
    { k = fun sk fk s -> m.k (fun x s -> (f x).k sk fk s) fk s }

  let unfailing (m : 'a Monad.t) : 'a opt =
    { k = fun sk _ s -> m.Monad.k sk s }

  let fail =
    { k = fun _ fk s -> fk s }

  let unfold (m : 'a opt) : 'a option opt =
    { k = fun sk _ s -> m.k (fun x s -> sk (Some x) s) (fun s -> sk None s) s }

  let recover (m : 'a opt) : 'a option Monad.t =
    { Monad.k = fun c s -> m.k (fun x s -> c (Some x) s) (fun s -> c None s) s }

  let run m =
    m.k (fun x s -> Value.return (Some (x,s))) (fun _ -> Value.return None) Name.AtomSet.empty
end

let (>>=) = Monad.(>>=)

let (>?=) = Opt.(>?=)

let (>!=) m f = (Opt.unfailing m) >?= f

let (>??=) m f = (Opt.unfold m) >?= f

let (>?>=) m f = (Opt.recover m) >>= f

(** A check is a postponed equality check.
    Pattern matching generates these. *)
type check =
  (* compare terms at a type *)
  | CheckEqual of Pattern.pterm * Tt.term * Tt.ty
  (* compare types in context *)
  | CheckEqualTy of ((Pattern.pty * Tt.ty), (Pattern.pty * Tt.ty)) Tt.abstraction

(* counter for debugging depth  *)
let cnt = let msg_cnt = ref (-1) in fun () -> (incr msg_cnt; !msg_cnt)

(** The whnf of a type [t] in environment [env]. *)
let rec whnf_ty env ctx (Tt.Ty t) : (Context.t * Tt.ty) Monad.t =
  whnf env ctx t >>= fun (ctx,t) ->
  Monad.return (ctx, Tt.ty t)

(** The "weak weak" head-normal form of a term [e] is obtained by ignoring the
    beta hints, sort of. They still get used in beta reductions for comparing
    the typing annotations. So it is a bit unclear what termination properties
    [weak_whnf] might have. There might be a tricky case in which we cycle
    because [beta_reduce] triggers [whnf] which triggers [weak_whnf].
    The important point is that it computes a form of [e] that is suitable
    for pattern-matching of the top-level constructor of [e]. *)
and weak_whnf env ctx e =
  let rec weak ctx ({Tt.term=e';assumptions; loc} as e) =
    begin match e' with
      | Tt.Spine (e, _, []) -> weak ctx (Tt.mention assumptions e)
      | Tt.Lambda ([], (e, _)) -> weak ctx (Tt.mention assumptions e)
      | Tt.Prod ([], Tt.Ty e) -> weak ctx (Tt.mention assumptions e)
      | Tt.Spine (e, (xts, t), (_::_ as es)) ->
        begin
          weak ctx e >>= fun (ctx, ({Tt.term=e';assumptions=_;loc=eloc} as e)) ->
          match e' with
          | Tt.Lambda (xus, (e', u)) ->
            begin
              beta_reduce ~loc:eloc env ctx xus e' u xts t es >?>= function
                | None -> Monad.return (ctx, Tt.mention assumptions (Tt.mk_spine ~loc e xts t es))
                | Some (ctx, e) -> weak ctx (Tt.mention assumptions e)
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
             Monad.return (ctx, Tt.mention assumptions (Tt.mk_spine ~loc e xts t es))
          | Tt.Bound _ ->
            Error.impossible ~loc "de Bruijn encountered in a spine head in whnf"
        end

      | Tt.Constant (x,es) ->
        let yts, _ =
          match Environment.lookup_constant x env with
            | Some ytsu -> ytsu
            | None -> Error.typing "unknown constant %t" (Name.print_ident x)
        in
        let rec fold ctx res yts es =
          begin match yts,es with
            | [], [] ->
              Monad.return (ctx, Tt.mention assumptions (Tt.mk_constant ~loc x (List.rev res)))
            | (y,(reducing,t))::yts, e::es ->
              begin if reducing
                then
                  whnf env ctx e
                else
                  Monad.return (ctx,e)
              end >>= fun (ctx,e) ->
              fold ctx (e::res) yts es
            | _::_,[] | [],_::_ ->
              Error.impossible ~loc "Invalid constant %t in weak_whnf" (Tt.print_term [] e)
          end
        in
        fold ctx [] yts es

      | Tt.Projection (e,xts,p) ->
        begin
          weak ctx e >>= fun (ctx, ({Tt.term=e';assumptions=_;loc=eloc} as e)) ->
          match e' with
            | Tt.Structure xtes ->
              begin
                projection_reduce ~loc:eloc env ctx xts p xtes >?>= function
                  | None -> Monad.return (ctx, Tt.mention assumptions (Tt.mk_projection ~loc e xts p))
                  | Some (ctx,e) -> weak ctx (Tt.mention assumptions e)
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
               Monad.return (ctx, Tt.mention assumptions (Tt.mk_projection ~loc e xts p))
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
      | Tt.Structure _ -> Monad.return (ctx, e)
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
  weak_whnf env ctx e >>= fun (ctx,e) ->
  let rec apply_beta = function
    | [] -> Monad.return (ctx, e)
    | ((ctxh, hyps, (xts, (p, e'))) as h) :: hs ->
      Print.debug "collecting for beta@ %t@ from@ %t"
        (Pattern.print_beta_hint [] h) (Tt.print_term [] e) ;
      (* XXX Here a failed join need not be fatal, we could catch and continue
         with the remaining hints *)
      let ctx = Context.join ~loc:(e.Tt.loc) ctxh ctx in
      (* Here we use beta hints. First we match [p] against [e]. *)
          (* XXX collect_* will Opt.return contexts *)
        collect_for_beta env ctx p e >?>= begin function
          | Some (pvars, checks, extras) ->
            (* we have a match, still need to verify validity of match *)
            Print.debug
              "Found a match of pattern@ %t@ against@ %t@, checking its \
               validity…"
              (Pattern.print_beta_hint xs h)
              (Tt.print_term xs e) ;
            begin verify_match ~spawn:false env ctx xts pvars checks >?>= function
            | None ->
              Print.debug "validity check failed";
              apply_beta hs (* not valid, try other hints *)
            | Some (ctx, es) ->
              (* success *)
              let e' = Tt.instantiate es e' in
              let e' = List.fold_left
                  (fun e ((yvs,w),es) -> Tt.mk_spine ~loc:(e.Tt.loc) e yvs w es) e' extras in
              Print.debug "beta hint@ %t@ matches@ %t,@ we get@ %t"
                (Pattern.print_beta_hint xs h)
                (Tt.print_term xs e)
                (Tt.print_term xs e') ;
              Monad.add_hyps hyps >>= fun () ->
              whnf env ctx e'
            end
          | None -> apply_beta hs (* did not match, try other hints *)
        end
  in
  if !Config.ignore_hints then Monad.return (ctx, e)
  else begin
    let key = Pattern.term_key e in
    Print.debug "trying beta hints for@ %t" (Tt.print_term xs e);
    apply_beta (Environment.beta_hints key env) >>= fun (ctx,e) ->
    Print.debug "%i found whnf@ %t )" i (Tt.print_term xs e);
    Monad.return (ctx, e)
  end

(** Beta reduction of [Lambda (xus, (e, u))] applied to arguments [es],
    where [(yvs, t)] is the typing annotation for the application.
    Opt.returns the resulting expression. *)
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
  equal_abstracted_ty env ctx xuvs u' t' >?= fun ctx ->
   let xus, (e, u) = Tt.instantiate_ty_abstraction Tt.instantiate_term_ty es' (xus, (e, u))
   and yvs, t = Tt.instantiate_ty_abstraction Tt.instantiate_ty es' (yvs, t) in
   let e = Tt.mk_lambda ~loc xus e u in
   let e = Tt.mk_spine ~loc e yvs t es in
   Opt.return (ctx, e)

(** Reduction of [{xtes}.p] at type [{xts}] *)
and projection_reduce ~loc env ctx xts p xtes =
  equal_signature ~loc env ctx xts (List.map (fun (l,x,t,_) -> l,x,t) xtes) >?= fun ctx ->
  let te = Tt.field_value ~loc xtes p in
  Opt.return (ctx,te)

(** Let [xuus] be the list [(x1,(u1,u1')); ...; (xn,(un,un'))] where
    [ui]  is well-formed in the context [x1:u1 , ..., x{i-1}:u{i-1} ] and
    [ui'] is well-formed in the context [x1:u1', ..., x{i-1}:u{i-1}'] and
    [v]  is well-formed in the context [x1:u1, ..., xn:un] and
    [v'] is well-formed in the context [x1:u1',..., xn:un'].
    We verify that the [ui] are equal to [ui'] and that [v] is equal to [v]. *)
and equal_abstracted_ty env ctx (xuus : (Name.ident * (Pattern.pty * Tt.ty)) list) v v' =
  (* As we descend into the contexts we carry around a list of variables
     [ys] with which we unabstract the bound variables. *)
  let rec eq env ctx ys ts =
    function
     | [] ->
        let v = Tt.unabstract_ty ys v
        and v' = Tt.unabstract_ty ys v' in
        equal_ty env ctx v v' >?= fun ctx ->
        Monad.lift (Value.context_abstract ~loc:Location.unknown ctx (List.rev ys) (List.rev ts)) >!= fun (ctx,ys,es) ->
        Monad.abstract_hyps ys es >!= fun () ->
        Opt.return ctx
     | (x,(u,u'))::xuus ->
        let u  = Tt.unabstract_ty ys u
        and u' = Tt.unabstract_ty ys u' in
        equal_ty env ctx u u' >?= fun ctx ->
        let ju = Judgement.mk_ty ctx u in
        let ctx, y, env = Environment.add_fresh ~loc:Location.unknown env x ju in
        eq env ctx (ys @ [y]) (ts @ [u]) xuus (* XXX optimize list append *)
  in
  eq env ctx [] [] xuus

(** Compare two types *)
and equal_ty env ctx (Tt.Ty t1) (Tt.Ty t2) = equal env ctx t1 t2 Tt.typ

and equal env ctx ({Tt.loc=loc1;_} as e1) ({Tt.loc=loc2;_} as e2) t =
  let xs = Environment.used_names env in
  let i = cnt () in
  Print.debug "(%i checking equality of@ %t@ and@ %t@ at type@ %t" i
    (Tt.print_term xs e1) (Tt.print_term xs e2) (Tt.print_ty xs t);
  let r =
  if Tt.alpha_equal e1 e2 then Opt.return ctx else
    begin (* type-directed phase *)
      whnf_ty env ctx t >!= fun (ctx, ((Tt.Ty {Tt.term=t';loc;_}) as t)) ->
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

              |  ((ctxh, hyps, (xts, (pt, k1, k2))) as h) :: hs ->
                let debug_i = cnt () in
                Print.debug "(%d collecting for eta %t" debug_i (Pattern.print_eta_hint [] h);
                (* XXX Here a failed join need not be fatal, we could catch and continue
                   with the remaining hints *)
                let ctx = Context.join ~loc ctxh ctx in
                collect_for_eta env ctx (pt, k1, k2) (t, e1, e2) >??= begin function
                  | None -> 
                     Print.debug "collecting for eta failed early %d)" debug_i;
                     fold hs (* no match, try other hints *)
                  | Some (pvars, checks) ->
                    (* check validity of the match *)
                    verify_match ~spawn:true env ctx xts pvars checks >??= begin function
                      | Some (ctx, _) ->
                         Print.debug "collecting for eta worked %d)" debug_i;
                         Monad.add_hyps hyps >!= fun () ->
                         Opt.return ctx (* success - notice how we throw away the witness of success *)
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
            let rec fold env ctx ys ts es =
              begin function
              | (x, ((Tt.Ty {Tt.loc=loc;_}) as v)) :: xvs ->
                  let v = Tt.unabstract_ty ys v in
                  let jv = Judgement.mk_ty ctx v in
                  let ctx, y, env =  Environment.add_fresh ~loc env x jv in
                  let e = Tt.mk_atom ~loc y in
                  fold env ctx (y :: ys) (v::ts) (e :: es) xvs
              | [] ->
                  let es = List.rev es in
                  let v = Tt.unabstract_ty ys u
                  and e1 = Tt.mk_spine ~loc:loc1 e1 xus u es
                  and e2 = Tt.mk_spine ~loc:loc2 e2 xus u es in
                  equal env ctx e1 e2 v >?= fun ctx ->
                  Monad.lift (Value.context_abstract ~loc:Location.unknown ctx ys ts) >!= fun (ctx,ys,es) ->
                  Monad.abstract_hyps ys es >!= fun () ->
                  Opt.return ctx
              end
            in fold env ctx [] [] [] xus

        | Tt.Eq _ -> Opt.return ctx (** Strict equality *)

        | Tt.Bracket _ -> Opt.return ctx (** Strict bracket types *)

        | Tt.Signature xts ->
          (* vs contains all the previous projections of e1 *)
          let rec fold ctx vs = function
            | [] -> Opt.return ctx
            | (l,x,t)::rem ->
              let t = Tt.instantiate_ty vs t in
              let e1 = Tt.mk_projection ~loc:loc1 e1 xts l in
              let e2 = Tt.mk_projection ~loc:loc2 e2 xts l in
              equal env ctx e1 e2 t >?= fun ctx ->
              fold ctx (e1::vs) rem
            in
          fold ctx [] xts

        | Tt.Bound _ -> Error.impossible ~loc:loc1 "deBruijn encountered in equal"

    end in
  r >??= fun b ->
  Print.debug "%i equality check %s)" i
    (match b with | None -> "failed" | Some _ -> "succeeded") ;
  r

(* Compare expressions at a given type [t] using general hints. *)
and equal_hints env ctx e1 e2 t =
  (* First we normalize the expressions *)
  (* XXX can break general hints on functions. First note that when we get
     here, eta expansion has already been applied. Now h : f ≡ λx.x will fail
     because the rhs [(λx.x) y] reduces to [y] but [f y] is stuck and h won't
     apply anymore *)
  whnf env ctx e1 >!= fun (ctx, ({Tt.term=e1';loc=loc1;_} as e1)) ->
  whnf env ctx e2 >!= fun (ctx, ({Tt.term=e2';loc=loc2;_} as e2)) ->
  (* short-circuit alpha equality *)
  if Tt.alpha_equal e1 e2 then
    Opt.return ctx
  else
    (* try general hints *)
    begin
      let key = Pattern.general_key e1 e2 t in
      Print.debug "Looking for a general hint with keys: %t" (Pattern.print_general_key key);

      let rec fold = function
        | ((ctxh, hyps, (xts, (pt, pe1, pe2))) as h) :: hs ->
           (* XXX Here a failed join need not be fatal, we could catch and continue
              with the remaining hints *)
           let ctx = Context.join ~loc:loc2 ctx ctxh in
           Print.debug "trying general hint@ %t" (Pattern.print_hint [] h);
           collect_for_hint env ctx (pt, pe1, pe2) (t, e1, e2) >??= begin function
           | None -> fold hs
           | Some (pvars, checks) ->
              (* check validity of the match *)
              Print.debug "verifying match";
              verify_match ~spawn:false env ctx xts pvars checks >??= begin function
              | Some (ctx, _) -> Opt.return ctx (* success - notice how we throw away the witness of success *)
              | None -> fold hs
              end
           end
        | [] -> Opt.fail
      in
      fold (if !Config.ignore_hints then [] else Environment.general_hints key env)
    end >??= begin function
    | None ->
       (* proceed with comparing the weak head normal forms *)
       equal_whnf env ctx e1 e2
    | Some ctx -> Opt.return ctx
    end

(* Compare normalized expressions. The assumption is that they both
   have a common type. *)
and equal_whnf env ctx ({Tt.term=e1';loc=loc1;_} as e1) ({Tt.term=e2';loc=loc2;_} as e2) =
  (* compare reduced expressions *)
  Print.debug "equal_whnf of %t and %t"
              (Tt.print_term [] e1)
              (Tt.print_term [] e2) ;
  match e1', e2' with

  | Tt.Atom x, Tt.Atom y ->
     if Name.eq_atom x y then Opt.return ctx
     else Opt.fail

  | Tt.Bound _, _ | _, Tt.Bound _ ->
     Error.impossible ~loc:loc1 "deBruijn encountered in equal_whnf"

  | Tt.Constant (x1, es1), Tt.Constant (x2, es2) ->
     if not @@ Name.eq_ident x1 x2
     then Opt.fail
     else
       let yts, _ =
         begin match Environment.lookup_constant x1 env with
         | Some ytsu -> ytsu
         | None -> Error.impossible "primitive application equality, unknown primitive operation %t" (Name.print_ident x1)
         end in
       let rec fold ctx es' yts es1 es2 =
         match yts, es1, es2 with
         | [], [], [] -> Opt.return ctx

         | (y,(reduce,t))::yts, e1::es1, e2::es2 ->
            if reduce
            then equal_whnf env ctx e1 e2
            else equal env ctx e1 e2 (Tt.instantiate_ty es' t)
              >?= fun ctx ->
              fold ctx (e1 :: es') yts es1 es2

         | _, _, _ ->
            Error.impossible ~loc:loc1 "primitive application equality (%d, %d, %d)"
              (List.length yts)
              (List.length es1)
              (List.length es2)
       in
       fold ctx [] yts es1 es2

  | Tt.Lambda (xus, (e1, t1)), Tt.Lambda (xvs, (e2, t2)) ->
     let rec zip ys ts env ctx = function
       | (x, u) :: xus, (_, u') :: xvs ->
          let u  = Tt.unabstract_ty ys u
          and u' = Tt.unabstract_ty ys u' in
          equal_ty env ctx u u' >?= fun ctx ->
          let ju = Judgement.mk_ty ctx u in
          let ctx, y, env = Environment.add_fresh ~loc:Location.unknown env x ju in
          zip (ys @ [y]) (ts @ [u]) env ctx (xus, xvs) (* XXX optimize list append *)

       | ([] as xus), xvs | xus, ([] as xvs) ->
          let t1' = Tt.mk_prod_ty ~loc:Location.unknown xus t1
          and t2' = Tt.mk_prod_ty ~loc:Location.unknown xvs t2 in
          let t1' = Tt.unabstract_ty ys t1'
          and t2' = Tt.unabstract_ty ys t2' in
          equal_ty env ctx t1' t2' >?= fun ctx ->
          let e1 = Tt.mk_lambda ~loc:(e1.Tt.loc) xus e1 t1
          and e2 = Tt.mk_lambda ~loc:(e2.Tt.loc) xvs e2 t2 in
          let e1 = Tt.unabstract ys e1
          and e2 = Tt.unabstract ys e2 in
          equal env ctx e1 e2 t1' >?= fun ctx ->
          Monad.lift (Value.context_abstract ~loc:Location.unknown ctx ys ts) >!= fun (ctx,ys,es) ->
          Monad.abstract_hyps ys es >!= fun () ->
          Opt.return ctx
     in
     zip [] [] env ctx (xus, xvs)

  | Tt.Spine (e1, xts1, es1), Tt.Spine (e2, xts2, es2) ->
     equal_spine ~loc:loc1 env ctx e1 (xts1, es1) e2 (xts2, es2)

  | Tt.Type, Tt.Type -> Opt.return ctx

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
     equal_ty env ctx u u' >?= fun ctx ->
     equal env ctx d1 d1' u >?= fun ctx ->
     equal env ctx d2 d2' u

  | Tt.Refl (u, d), Tt.Refl (u', d') ->
     equal_ty env ctx u u' >?= fun ctx ->
     equal env ctx d d' u

  | Tt.Inhab t, Tt.Inhab t' ->
     equal_ty env ctx t t'

  | Tt.Bracket t1, Tt.Bracket t2 ->
     equal_ty env ctx t1 t2

  | Tt.Signature xts1, Tt.Signature xts2 -> equal_signature ~loc:loc1 env ctx xts1 xts2

  | Tt.Structure xtes1, Tt.Structure xtes2 ->
    let xts1 = List.map (fun (l,x,t,_) -> l,x,t) xtes1 in
    let xts2 = List.map (fun (l,x,t,_) -> l,x,t) xtes2 in
    equal_signature ~loc:loc1 env ctx xts1 xts2 >?= fun ctx ->
    equal_module ~loc:loc1 env ctx xtes1 xtes2

  | Tt.Projection (te1,xts1,p1), Tt.Projection (te2,xts2,p2) ->
    if Name.eq_ident p1 p2
    then
      equal_signature ~loc:loc1 env ctx xts1 xts2 >?= fun ctx ->
      equal_whnf env ctx te1 te2
    else Opt.fail

  | (Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Spine _ |
     Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _ |
     Tt.Signature _ | Tt.Structure _ | Tt.Projection _), _ ->
     Opt.fail

and equal_spine ~loc env ctx e1 a1 e2 a2 =
  (* We deal with nested spines. They are nested in an inconvenient way so
     we first get them the way we need them. *)
  let rec collect_spines ab abs n ({Tt.term=e';_} as e) =
    match e' with
    | Tt.Spine (e, xts, es) -> collect_spines (xts,es) (ab :: abs) (n + List.length es) e
    | _ -> e, ab, abs, n
  in
  let h1, a1, as1, n1 = collect_spines a1 [] (List.length (snd a1)) e1
  and h2, a2, as2, n2 = collect_spines a2 [] (List.length (snd a2)) e2 in
  if not (n1 = n2)
  then Opt.fail
  else
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
              equal_ty env ctx u1 u2 >?=
              (* Compare the spine heads. We postpone doing so until
                 we have checked that they have the same type, which
                 we did because we compared [u1] and [u2] as well as
                 the types of all the binders we encountered *)
              fun ctx -> equal_whnf env ctx h1 h2

           | ((xts1, v1), ds1) :: as1 ->
              let u1 = Tt.instantiate_ty es1 u1 in
              let u1' = Tt.mk_prod_ty ~loc xts1 v1 in
              equal_ty env ctx u1 u1' >?=
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
              equal_ty env ctx u2 u2' >?=
              (* we may flatten spines and proceed with equality check *)
              fold es1 [] ((xts1, u1), ds1) as1 ((xts2, v2), ds2) as2
              (* else we may not flatten the spine *)
              (* XXX think what to do here really *)
        end

      | ((x1,t1) :: xts1, e1::ds1), ((x2,t2)::xts2, e2::ds2) ->
        let t1 = Tt.instantiate_ty es1 t1
        and t2 = Tt.instantiate_ty es2 t2 in
        equal_ty env ctx t1 t2 >?=
        fun ctx -> equal env ctx e1 e2 t1 >?=
        begin
          let es1 = e1 :: es1
          and es2 = e2 :: es2
          in
          fold es1 es2 ((xts1, u1), ds1) as1 ((xts2, u2), ds2) as2
        end

      | ([], _::_), _ | (_::_, []), _ | _, ([], _::_) | _, (_::_, []) ->
        Error.impossible "Equal.equal_spine encountered an invalid spine"
    in
    fold [] [] a1 as1 a2 as2 ctx
  end

and equal_signature ~loc env ctx xts1 xts2 =
  let rec fold env ctx ys ts xts1 xts2 = match xts1, xts2 with
    | [], [] ->
      Monad.lift (Value.context_abstract ~loc ctx ys ts) >!= fun (ctx,ys,es) ->
      Monad.abstract_hyps ys es >!= fun () ->
      Opt.return ctx
    | (l1,x,t1)::xts1, (l2,_,t2)::xts2 ->
      if Name.eq_ident l1 l2
      then
        let t1 = Tt.unabstract_ty ys t1 in
        let t2 = Tt.unabstract_ty ys t2 in
        equal_ty env ctx t1 t2 >?= fun ctx ->
        let jx = Judgement.mk_ty ctx t1 in
        let ctx, y, env = Environment.add_fresh ~loc env x jx in
        fold env ctx (y::ys) (t1::ts) xts1 xts2
      else Opt.fail
    | _::_,[] | [],_::_ -> Opt.fail
    in
  fold env ctx [] [] xts1 xts2

(** this function assumes that the derived signatures have already been checked equal label to label *)
and equal_module ~loc env ctx xtes1 xtes2 =
  let rec fold ctx vs xtes1 xtes2 = match xtes1, xtes2 with
    | [], [] ->
      Opt.return ctx
    | (l1,x,t1,te1)::xts1, (l2,_,t2,te2)::xts2 ->
      if Name.eq_ident l1 l2
      then
        let ty = Tt.instantiate_ty vs t1 in (* here we need to know that ctx |- instantiate t1 == instantiate t2. Is this true? *)
        let te1 = Tt.instantiate vs te1 in
        let te2 = Tt.instantiate vs te2 in
        equal env ctx te1 te2 ty >?= fun ctx ->
        fold ctx (te1::vs) xts1 xts2
      else Opt.fail
    | _::_,[] | [],_::_ -> Opt.fail
    in
  fold ctx [] xtes1 xtes2

(** [pattern_collect env p ?t e] matches pattern [p] against term [e]
    of possibly given type [t].

    It outputs two lists [pvars] and [checks].
    The list [pvars] maps pattern variables to the terms they were
    matched against. The list [checks] contains equalities which
    must be verified before the match is considered valid.
    It raises [NoMatch] if there is a mismatch. *)

and pattern_collect env ctx p ~at_ty e =
    Print.debug "collecting %t" (Tt.print_term [] e) ;
    whnf env ctx e >!= fun (ctx, e) ->
    pattern_collect_whnf env ctx p ~at_ty e

(* Collect from [e] assuming it is in whnf. *)
and pattern_collect_whnf env ctx p ~at_ty ({Tt.term=e';loc;_} as e_orig) =
  Print.debug "collecting pattern %t from whnf %t"
    (Pattern.print_pattern [] ([],p)) (Tt.print_term [] e_orig) ;
  match p with

  | Pattern.Atom x' ->
    begin match e' with
    | Tt.Atom x -> if Name.eq_atom x' x then Opt.return ([], []) else Opt.fail
    | _ -> Opt.fail
    end

  | Pattern.PVar k ->
    Opt.return ([(k, (e_orig, at_ty))], [])

  | Pattern.Constant (x, pes) ->
    begin match e' with
      | Tt.Constant (y, es) -> collect_primapp ~loc env ctx x pes y es
      | _ -> Opt.fail
    end

  | Pattern.Spine (pe, (xts, u), pes) ->
    begin match e' with
      | Tt.Spine (e, (yus, v), es) ->
        pattern_collect_spine ~loc env ctx (pe, (xts, u), pes) (e, (yus, v), es) >?= fun (pvars, checks, extras) ->
        begin match extras with
        | _::_ ->
          Print.debug "found unexpected trailing arguments at %t"
            (Tt.print_term (Environment.used_names env) e_orig);
          Opt.fail
        | [] ->
          Print.debug "no trailing arguments for %t"
            (Tt.print_term (Environment.used_names env) e_orig);
          Opt.return (pvars, checks)
        end
      | _ -> Opt.fail
    end

  | Pattern.Eq (pt, pe1, pe2) ->
    begin match e' with
      | Tt.Eq (t, e1, e2) ->
        pattern_collect_ty env ctx pt t >?= fun (pvars_t, checks_t) ->
        pattern_collect env ctx pe1 ~at_ty:t e1 >?= fun (pvars_e1, checks_e1) ->
        pattern_collect env ctx pe2 ~at_ty:t e2 >?= fun (pvars_e2, checks_e2) ->
        Opt.return (pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2)
      | _ -> Opt.fail
    end

  | Pattern.Refl (pt, pe) ->
    begin match e' with
      | Tt.Refl (t, e) ->
        pattern_collect_ty env ctx pt t >?= fun (pvars_t, checks_t) ->
        pattern_collect env ctx pe ~at_ty:t e >?= fun (pvars_e, checks_e) ->
        Opt.return (pvars_t @ pvars_e, checks_t @ checks_e)
      | _ -> Opt.fail
    end

  | Pattern.Bracket pt ->
    begin match e' with
      | Tt.Bracket t -> pattern_collect_ty env ctx pt t
      | _ -> Opt.fail
    end

  | Pattern.Term (e',t') ->
    Opt.return ([], [CheckEqualTy ([], (t', at_ty)); CheckEqual (e', e_orig, at_ty)])

(* Collect from a type. *)
and pattern_collect_ty env ctx (Pattern.Ty p) (Tt.Ty e) =
  pattern_collect env ctx p ~at_ty:Tt.typ e

(* Collect pattern variables from a spine, and Opt.return trailing arguments.
   Also account for nested spines. *)
and pattern_collect_spine ~loc env ctx (pe, xtsu, pes) (e, yvsw, es) =

  (* We deal with nested spines. They are nested in an inconvenient way so
     we first get them the way we need them. *)
  let rec collect_spines_terms ab abs n ({Tt.term=e';_} as e) =
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
  begin if n1 > n2 then Opt.fail else Opt.return ()
  end >?= fun () ->

  (* match the heads *)
  (* The type comes from the *term* not the pattern and thus doesn't contain pvars *)
  begin
    let t = (let ((yvs, w), _) = args in Tt.mk_prod_ty ~loc yvs w) in
    pattern_collect_whnf env ctx ph ~at_ty:t h
  end >?= fun (pvars_head, checks_head) ->

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
      pattern_collect env ctx pe ~at_ty:v e >?= fun (pvars_e, checks_e) ->
      let xtvs = (x,(t,v)) :: xtvs in
      let es' = e :: es' in
      fold xtvs es' ((xts, u), pes) pargss ((yvs, w), es) argss >?= fun (pvars, checks, extras) ->
        Opt.return (pvars_e @ pvars, checks_e @ checks, extras)

    | ((_::_) as xts), ((_::_) as pes), [], [] ->
      begin
        match argss with
        | [] -> Error.impossible ~loc "invalid spine in pattern match (1)"
        | ((yvs, w'), es) :: argss ->
          let t1 = Tt.instantiate_ty es' w
          and t2 = Tt.mk_prod_ty ~loc yvs w' in
          equal_ty env ctx t1 t2 >?= fun ctx ->
          fold xtvs es' ((xts,u), pes) pargss ((yvs, w'), es) argss
      end

    | [], [], _::_, _::_ ->
      begin
        let xtvs = List.rev xtvs in

        let u = Tt.instantiate_ty es' u
        and yvs, w = Tt.instantiate_ty_abstraction Tt.instantiate_ty es' (yvs, w) in
        let w_prod = Tt.mk_prod_ty ~loc yvs w in

        let check_uw = CheckEqualTy (xtvs, (u, w_prod)) in
        match pargss with
        | [] -> Opt.return ([], [check_uw], ((yvs, w), es) :: argss)
        | pargs :: pargss ->
          fold [] [] pargs pargss ((yvs, w), es) argss >?= fun (pvars, checks, extras) ->
          Opt.return (pvars, check_uw :: checks, extras)
      end

    | [], [], [], [] ->
      begin
        let xtvs = List.rev xtvs in
        (* the Opt.return types may still contain variables bound to the arguments
           of the spine; instantiate them. *)
        let w = Tt.instantiate_ty es' w in
        let u = Tt.instantiate_ty es' u in

        let check_uw = CheckEqualTy (xtvs, (u, w)) in
          match pargss, argss with
            | [], argss -> Opt.return ([], [check_uw], argss)
            | pargs::pargss, args::argss ->
              fold [] [] pargs pargss args argss >?= fun (pvars, checks, extras) ->
                Opt.return (pvars, check_uw :: checks, extras)
            | _::_, [] -> Error.impossible ~loc "invalid spine in pattern match (2)"
      end

    | [], _::_, _, _ | _::_, [], _, _ ->
      Error.impossible ~loc "invalid spine pattern encountered in pattern collection"
    | _, _, [], _::_ | _, _, _::_, [] ->
      Error.impossible ~loc "invalid spine encountered in pattern collection"
  in
  fold [] [] pargs pargss args argss >?= fun (pvars, checks, extras) ->
    Opt.return (pvars_head @ pvars, checks_head @ checks, extras)

(** Collect values of pattern variables by matching a beta
    pattern [bp] against whnf expression [e]. Also Opt.return the residual
    equations that remain to be checked, and the unused
    arguments. *)
and collect_for_beta env ctx bp {Tt.term=e';loc;_} =
  match bp, e' with

  | Pattern.BetaAtom x, Tt.Atom y ->
    if Name.eq_atom x y
    then Opt.return ([], [], [])
    else Opt.fail

  | Pattern.BetaAtom x, Tt.Spine (e, yts, es) ->
    let rec fold args {Tt.term=e';_} yts es =
      match e' with
        | Tt.Atom y ->
          if Name.eq_atom x y
          then Opt.return ((yts, es) :: args)
          else Opt.fail
        | Tt.Spine (e', yts', es') ->
          fold ((yts, es) :: args) e' yts' es'
        | _ -> Opt.fail    (* XXX remove catch-all *)
    in
    fold [] e yts es >?= fun extras ->
    Opt.return ([], [], extras)

  | Pattern.BetaConstant (x, pes), Tt.Spine (e, yts, es) ->
    Print.debug "collect_beta for %t" (Name.print_ident x) ;
    let rec fold extras {Tt.term=e';_} yts es =
      match e' with
        | Tt.Constant (y, es') ->
           let extras = (yts, es) :: extras in
           let extras = List.rev extras in
           Opt.return (y, es', extras)
        | Tt.Spine (e', yts', es') -> fold ((yts, es) :: extras) e' yts' es'
        | _ -> Opt.fail
    in
    fold [] e yts es >?= fun (y, es, extras) ->
    collect_primapp ~loc env ctx x pes y es >?= fun (pvars, checks) ->
    Print.debug "collect_beta for %t WORKED" (Name.print_ident x) ;
    Opt.return (pvars, checks, extras)

  | Pattern.BetaConstant (x, pes), Tt.Constant (y, es) ->
     collect_primapp ~loc env ctx x pes y es >?= fun (pvars, checks) ->
     Opt.return (pvars, checks, [])

  | Pattern.BetaSpine (pe, xts, pes), Tt.Spine (e, yts, es) ->
    pattern_collect_spine ~loc env ctx (pe, xts, pes) (e, yts, es)

  | (Pattern.BetaAtom _ | Pattern.BetaSpine _ | Pattern.BetaConstant _), _ ->
    Opt.fail

and collect_primapp ~loc env ctx x pes y es =
  if not (Name.eq_ident x y)
  then Opt.fail
  else begin
    let yts, _ =
      begin match Environment.lookup_constant x env with
            | Some ytsu -> ytsu
            | None -> Error.impossible ~loc "unknown operation %t in pattern_collect" (Name.print_ident x)
      end in
    let rec fold es' yts pes es =
      match yts, pes, es with
      | [], [], [] -> Opt.return ([], [])

      | (y,(reducing,t))::yts, pe::pes, e::es ->
          begin
            let t = Tt.instantiate_ty es' t in
            if reducing
            then pattern_collect_whnf env ctx pe ~at_ty:t e
            else pattern_collect      env ctx pe ~at_ty:t e
          end >?= fun (pvars_e, checks_e) ->
         fold (e::es') yts pes es >?= fun (pvars,checks) ->
         Opt.return (pvars_e @ pvars, checks_e @ checks)

      | _, _, _ ->
         Error.impossible ~loc "malformed primitive applications in pattern_collect"
    in
    fold [] yts pes es
  end

(** Similar to [collect_for_beta] except ctx targeted at extracting
  values of pattern variable and residual equations in eta hints,
  where we compare a type and two terms. *)
and collect_for_eta env ctx (pt, k1, k2) (t, e1, e2) =
  pattern_collect_ty env ctx pt t >?= fun (pvars_t,  checks_t) ->
    Opt.return ((k1,(e1,t)) :: (k2,(e2,t)) :: pvars_t, checks_t)

and collect_for_hint env ctx (pt, pe1, pe2) (t, e1, e2) =
  pattern_collect_ty env ctx pt t >?= fun (pvars_t, checks_t) ->
  pattern_collect env ctx pe1 ~at_ty:t e1 >?= fun (pvars_e1, checks_e1) ->
  pattern_collect env ctx pe2 ~at_ty:t e2  >?= fun (pvars_e2, checks_e2) ->
  Opt.return (pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2)

and collect_for_inhabit env ctx pt t =
  pattern_collect_ty env ctx pt t

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
     try to inhabit it when [spawn] is [true]. Opt.return a list of
     inhabitation problems that need to be checked later for this
     match to be successful. *)
  let rec subst_of_pvars env ctx pvars k xts es inhs =
    match xts with
    | [] -> Opt.return (ctx, es, inhs)
    | (_,t) :: xts ->
      begin match lookup k pvars with

        | Some (e,t') ->
          (* Pattern variable [k] is matched to [e] of type [t'].
             We need to verify that [t] and [t'] are equal. *)
          let t = Tt.instantiate_ty es t in
          Print.debug "matching: compare %t and %t (es %d)" (Tt.print_ty [] t) (Tt.print_ty [] t') (List.length es);
          equal_ty env ctx t t' >?= fun ctx ->
          subst_of_pvars env ctx pvars (k-1) xts (e :: es) inhs

        | None ->
          if not spawn
          then Opt.fail (* we are not supposed to instantiate missing variables *)
          else begin
            (* Try to inhabit the type [t]. Actually, we first calculate the
               only possible candidate, and redo the check later when we actually
               know that the pattern match will succeed. *)
            let t = Tt.instantiate_ty es t in
            Print.debug "matching: trying to inhabit@ %t" (Tt.print_ty [] t) ;
            inhabit ~subgoals:false env ctx t >?= fun (ctx,e) ->
            subst_of_pvars env ctx pvars (k-1) xts (e :: es) ((env,t) :: inhs)
          end
      end
  in

  (* Make a substitution from the collected [pvars] *)
  subst_of_pvars env ctx pvars (List.length xts - 1) xts [] [] >?= fun (ctx, es, inhs) ->
  Print.debug "built substitution %d" debug_i;
  (* Perform the equality checks to validate the match *)
  List.fold_left
    (fun mctx check -> mctx >?= fun ctx -> match check with
       | CheckEqual (e1, e2, t) ->
          let e1 = Tt.instantiate es e1 in
          Print.debug "CheckEqual at@ %t@ %t@ %t"
            (Tt.print_ty (Environment.used_names env) t)
            (Tt.print_term (Environment.used_names env) e1)
            (Tt.print_term (Environment.used_names env) e2);
          equal_whnf env ctx e1 e2

       | CheckEqualTy (xuvs, (t1, t2)) ->

          (* All de Bruijn indices refer to pvars from the point of view of
             the body, we therefore must not instantiate with
             [Tt.instantiate_abstraction] which expects them to be relative to
             the current abstraction *)
          let xuvs = List.map (fun (x, (pt, t)) -> x, (Tt.instantiate_ty es pt, t)) xuvs in
          let t1', t2' =  Tt.instantiate_ty es t1, t2 in

          Print.debug "%d es: %t" debug_i
            (Print.sequence (Tt.print_term ~max_level:0 []) "; " es);

          Print.debug "%d instantiated pattern Opt.return type@ %t@ as@ %t" debug_i
            (Tt.print_ty [] t1)
            (Tt.print_ty [] t1') ;

          Print.debug "%d instantiated rhs-term Opt.return type@ %t@ as@ %t" debug_i
            (Tt.print_ty [] t2)
            (Tt.print_ty [] t2') ;

          Print.debug "%d CheckEqualTy@ %t@ %t" debug_i
            (Tt.print_ty [] t1')
            (Tt.print_ty [] t2');
          equal_abstracted_ty env ctx xuvs t1' t2')
    (Opt.return ctx)
    checks >?= fun ctx ->
  (* Perform delayed inhabitation goals *)
  (* XXX why is it safe to delay these? *)
  List.fold_left
    (fun mctx (env, t) -> mctx >?= fun ctx ->
       inhabit ~subgoals:true env ctx t >?= fun (ctx,_) ->
       Opt.return ctx)
     (Opt.return ctx)
     inhs >?= fun ctx ->
  (* match succeeded *)
  Print.debug "succeeded %d)" debug_i ;
  Opt.return (ctx, es)

and as_bracket env (ctx, t) =
  whnf_ty env ctx t >>= fun (ctxt, Tt.Ty {Tt.term=t';loc;_}) ->
  match t' with
  | Tt.Bracket t -> Monad.return (ctxt, t)
  | _ -> Error.typing ~loc "[] has a bracket type and not %t" (Tt.print_ty (Environment.used_names env) t)

(** Strip brackets from a given type. *)
and strip_bracket env ctx t =
  whnf_ty env ctx t >>= fun (ctx, Tt.Ty {Tt.term=t';loc;_}) ->
  match t' with
  | Tt.Bracket t -> strip_bracket env ctx t
  | _ ->  Monad.return (ctx, t) (* XXX or should be Opt.return the whnf t? *)

(** Try to inhabit the given type [t], which must be proof-irrelevant.
    If [subgoals] is [true] then recursively resolve goals, otherwise
    just Opt.return the only possible inhabitant of [t]. *)
and inhabit ~subgoals env ctx t =
  whnf_ty env ctx t >!= fun (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) ->
  inhabit_whnf ~subgoals env ctx t

and inhabit_whnf ~subgoals env ctx ((Tt.Ty {Tt.term=t';loc;_}) as t) =
  Print.debug "trying to inhabit (subgoals = %b) whnf@ %t"
    subgoals (Tt.print_ty [] t);
  match t' with

    | Tt.Prod (xts', t') ->
      let rec fold env ctx ys ts = function
        | [] ->
          let t' = Tt.unabstract_ty ys t' in
          inhabit ~subgoals env ctx t' >?= fun (ctx,e) ->
          Monad.lift (Value.context_abstract ~loc ctx ys ts) >!= fun (ctx,zs,es) ->
          Monad.abstract_hyps zs es >!= fun () ->
          let e = Tt.abstract ys (Tt.substitute zs es e) in
          let e = Tt.mk_lambda ~loc xts' e t' in
          Opt.return (ctx, e)
        | (x,t)::xts ->
          let t = Tt.unabstract_ty ys t in
          let jt = Judgement.mk_ty ctx t in
          let ctx, y, env = Environment.add_fresh ~loc env x jt in
          fold env ctx (y :: ys) (t::ts) xts
      in
        fold env ctx [] [] xts'

    | Tt.Eq (t, e1, e2) ->
       if not subgoals
       then
         (* Do not create new subgoals, just Opt.return the only
            possible candidate for inhabitation. *)
         let e = Tt.mk_refl ~loc t e1 in
         Opt.return (ctx, e)
       else
         equal env ctx e1 e2 t >?= fun ctx ->
           let e = Tt.mk_refl ~loc t e1 in
           Opt.return (ctx, e)

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
    | Tt.Type -> Opt.fail

and inhabit_bracket ~subgoals ~loc env (ctx, t_inhabit) =
  if not subgoals then
    Opt.return (ctx, Tt.mk_inhab ~loc t_inhabit)
  else
    (* apply inhabit hints *)
    strip_bracket env ctx t_inhabit >!= fun (ctx, t) ->
    let key = Pattern.ty_key t in
    let rec fold = function
      | [] -> Opt.fail
      | ((ctxh, hyps, (xts, pt)) as h) :: hs ->
         Print.debug "attempting to inhabit@ %t using@ %t"
                     (Tt.print_ty [] t) (Pattern.print_inhabit_hint [] h) ;
         (* XXX Here a failed join need not be fatal, we could catch and continue
            with the remaining hints *)
         let ctx = Context.join ~loc ctx ctxh in
         collect_for_inhabit env ctx pt t >??= begin function
         | None -> fold hs
         | Some (pvars, checks) ->
            (* check validity of the match *)
            verify_match ~spawn:true env ctx xts pvars checks >??= begin function
                  | Some (ctx, _) ->
                    Monad.add_hyps hyps >!= fun () ->
                    Opt.return (ctx, Tt.mk_inhab ~loc t_inhabit)
                  | None -> fold hs
            end
         end
    in fold (Environment.inhabit_hints key env)

let as_atom env (ctx, e', t)  =
  whnf env ctx e' >>= fun (ctx, {Tt.term=e';loc;_}) ->
  match e' with
  | Tt.Atom x -> Monad.return (ctx, x, t)
  | Tt.Prod _ | Tt.Type | Tt.Eq _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ ->
    Error.runtime ~loc "this expression should be an atom"

let rec deep_prod env ctx t f =
  whnf_ty env ctx t >>= fun (ctx, (Tt.Ty ({Tt.term=t';loc;_} as t))) ->
  match t' with

  | Tt.Prod ([], _) -> Error.impossible ~loc "empty product encountered in deep_prod"

  | Tt.Prod ((_ :: _) as xus, w) ->

     let rec fold env ctx ys ts zvs =
       begin match zvs with
       | [] ->
          let w = Tt.unabstract_ty ys w in
          deep_prod env ctx w f >>= fun (ctx, (zvs, w)) ->
          Monad.lift (Value.context_abstract ~loc ctx ys ts) >>= fun (ctx,zs,es) ->
          Monad.abstract_hyps zs es >>= fun () ->
          let zvs_w = Tt.substitute_ty_abstraction Tt.substitute_ty zs es (zvs,w) in
          let (zvs, w) = Tt.abstract_ty_abstraction Tt.abstract_ty ys zvs_w in
          Monad.return (ctx, (xus @ zvs, w))

       | (z,v) :: zvs ->
          let v = Tt.unabstract_ty ys v in
          let jv = Judgement.mk_ty ctx v in
          let ctx, y, env = Environment.add_fresh ~loc env z jv in
          fold env ctx (y :: ys) (v::ts) zvs
       end in

     fold env ctx [] [] xus

  | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Eq _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ ->
     f env ctx (Tt.ty t) >>= fun (ctx,t) ->
     Monad.return (ctx, ([], t))

let as_prod env (ctx, t) = deep_prod env ctx t (fun env ctx x -> Monad.return (ctx, x))

let as_eq env (ctx, ((Tt.Ty {Tt.loc=loc;_}) as t)) =
  whnf_ty env ctx t >>= fun (ctx, Tt.Ty {Tt.term=t';_}) ->
  match t' with

  | Tt.Eq (t, e1, e2) -> Monad.return (ctx, t, e1, e2)

  | Tt.Prod _ | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ ->
     Error.typing ~loc
       "this expression should be an equality type, found@ %t"
       (Tt.print_ty [] t)


let as_universal_eq env (ctx, ((Tt.Ty {Tt.loc=loc;_}) as t)) =
  as_prod env (ctx, t) >>= fun (ctx, (xus, (Tt.Ty {Tt.term=t';loc;_} as t))) ->
  match t' with

  | Tt.Eq (t, e1, e2) ->
     Monad.return (ctx, (xus, (t, e1, e2)))

  | Tt.Prod _ -> Error.impossible ~loc "product encountered in as_universal_eq"

  | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Refl _ | Tt.Inhab _ | Tt.Bracket _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ ->
     Error.typing ~loc
       "the type of this expression should be a universally quantified equality, found@ %t"
       (Tt.print_ty [] t)

let as_universal_bracket env (ctx, ((Tt.Ty {Tt.loc=loc;_}) as t)) =
  deep_prod
    env ctx t
    (fun env ctx ((Tt.Ty {Tt.term=t';loc;_}) as t) ->
     match t' with

     | Tt.Bracket t -> strip_bracket env ctx t

     | Tt.Prod _ -> Error.impossible ~loc "product encountered in as_universal_bracket"

     | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
     | Tt.Spine _ | Tt.Refl _ | Tt.Inhab _
     | Tt.Signature _ | Tt.Structure _ | Tt.Projection _
     | Tt.Eq _ -> Monad.return (ctx, t))


let as_signature env (ctx, t) =
  whnf_ty env ctx t >>= fun (ctxt, Tt.Ty {Tt.term=t';loc;_}) ->
  match t' with
    | Tt.Signature xts -> Monad.return (ctxt, xts)
    | _ -> Error.typing ~loc
      "this expressing should be a signature, found@ %t"
      (Tt.print_ty [] t)

