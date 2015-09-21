(** Equality checking and weak-head-normal-forms *)

(** A check is a postponed equality check.
    Pattern matching generates these. *)
type check =
  | CheckEqual of Pattern.pterm * Tt.term * Tt.ty (* compare terms at a type *)
  | CheckEqualTy of (Pattern.pty * Tt.ty, Pattern.pty * Tt.ty) Tt.abstraction (* compare types in context *)
  | CheckAlphaEqual of Pattern.pterm * Tt.term (* compare terms for alpha equality *)

(* counter for debugging depth  *)
let cnt = let msg_cnt = ref (-1) in fun () -> (incr msg_cnt; !msg_cnt)

(** Alpha equality *)
(* Currently, the only difference between alpha and structural equality is that
   the names of variables in abstractions are ignored. *)
let alpha_equal_abstraction alpha_equal_u alpha_equal_v (xus, v) (xus', v') =
  let rec eq xus xus' =
    match xus, xus' with
    | [], [] -> true
    | (_, u) :: xus, (_, u') :: xus' ->
        alpha_equal_u u u' &&
        eq xus xus'
    | [], _::_ | _::_, [] -> false
  in
  eq xus xus' &&
  alpha_equal_v v v'

let rec alpha_equal (e1,_) (e2,_) =
  e1 == e2 || (* a shortcut in case the terms are identical *)
  begin match e1, e2 with

    | Tt.Atom x, Tt.Atom y -> Name.eq_atom x y

    | Tt.Bound i, Tt.Bound j -> i = j

    | Tt.Constant (x, es), Tt.Constant (x', es') ->
      Name.eq_ident x x' &&
      alpha_equal_list alpha_equal es es'

    | Tt.Lambda abs, Tt.Lambda abs' ->
      alpha_equal_abstraction alpha_equal_ty alpha_equal_term_ty abs abs'

    | Tt.Spine (e, xts, es), Tt.Spine (e', xts', es') ->
      alpha_equal e e' &&
      alpha_equal_abstraction alpha_equal_ty alpha_equal_ty xts xts' &&
      alpha_equal_list alpha_equal es es'

    | Tt.Type, Tt.Type -> true

    | Tt.Prod abs, Tt.Prod abs' ->
      alpha_equal_abstraction alpha_equal_ty alpha_equal_ty abs abs'

    | Tt.Eq (t, e1, e2), Tt.Eq (t', e1', e2') ->
      alpha_equal_ty t t' &&
      alpha_equal e1 e1' &&
      alpha_equal e2 e2'

    | Tt.Refl (t, e), Tt.Refl (t', e') ->
      alpha_equal_ty t t' &&
      alpha_equal e e'

    | Tt.Bracket t1, Tt.Bracket t2 ->
      alpha_equal_ty t1 t2

    | Tt.Inhab, Tt.Inhab -> true

    | (Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _ | Tt.Spine _ |
        Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _ | Tt.Bracket _ | Tt.Inhab), _ ->
      false
  end

and alpha_equal_ty (Tt.Ty t1) (Tt.Ty t2) = alpha_equal t1 t2

and alpha_equal_term_ty (e, t) (e', t') = alpha_equal e e' && alpha_equal_ty t t'

and alpha_equal_list equal_e es es' =
  match es, es' with
  | [], [] -> true
  | e :: es, e' :: es' ->
    equal_e e e' && alpha_equal_list equal_e es es'
  | ([],_::_) | ((_::_),[]) -> false

(** Indicate a mismatch during pattern matching -- only used locally and should
    never escape [verify_match] or [collect_for_XXX] below. *)
exception NoMatch

(** The whnf of a type [t] in context [ctx]. *)
let rec whnf_ty ctx (Tt.Ty t) =
  let t = whnf ctx t
  in Tt.ty t

(** The "weak weak" head-normal form of a term [e] is obtained by ignoring the
    beta hints, sort of. They still get used in beta reductions for comparing
    the typing annotations. So it is a bit unclear what termination properties
    [weak_whnf] might have. There might be a tricky case in which we cycle
    because [beta_reduce] triggers [whnf] which triggers [weak_whnf].
    The important point is that it computes a form of [e] that is suitable
    for pattern-matching of the top-level constructor of [e]. *)
and weak_whnf ctx ((e', loc) as e) =
  let rec weak ((e', loc) as e) =
    begin match e' with
      | Tt.Spine (e, _, []) -> weak e
      | Tt.Lambda ([], (e, _)) -> weak e
      | Tt.Prod ([], Tt.Ty e) -> weak e
      | Tt.Spine (e, (xts, t), (_::_ as es)) ->
        begin
          let (e',eloc) as e = weak e in
          match e' with
          | Tt.Lambda (xus, (e', u)) ->
            begin
              match beta_reduce ~loc:eloc ctx xus e' u xts t es with
              | None -> Tt.mk_spine ~loc e xts t es
              | Some e -> weak e
            end
          | Tt.Atom _
          | Tt.Constant _
          | Tt.Spine _
          | Tt.Type
          | Tt.Prod _
          | Tt.Eq _
          | Tt.Refl _
          | Tt.Inhab
          | Tt.Bracket _ ->
            Tt.mk_spine ~loc e xts t es
          | Tt.Bound _ ->
            Error.impossible ~loc "de Bruijn encountered in a spine head in whnf"
        end

      | Tt.Constant _ ->
        (* XXX here we shall use info about primitive operations to normalize some
           of their arguments. *)
        e

      | Tt.Lambda (_ :: _, _)
      | Tt.Prod (_ :: _, _)
      | Tt.Atom _
      | Tt.Type
      | Tt.Eq _
      | Tt.Refl _
      | Tt.Inhab
      | Tt.Bracket _ -> e
      | Tt.Bound _ ->
          Error.impossible ~loc "de Bruijn encountered in weak_whnf"
    end
  in
  weak e

(** The whnf of term [e] in context [ctx], assuming [e] has a type.
    Here we use available beta hints. *)
and whnf ctx e =
  let i = cnt () in
  let xs = Context.used_names ctx in
  Print.debug "(%i computing whnf of@ %t@ " i (Tt.print_term xs e);
  let e = weak_whnf ctx e in
  let xs = Context.used_names ctx in
  let rec apply_beta = function
    | [] -> e
    | ((xts, (p, e')) as h) :: hs ->
      Print.debug "collecting for beta@ %t@ from@ %t"
        (Pattern.print_beta_hint [] h) (Tt.print_term [] e) ;
      (* Here we use beta hints. First we match [p] against [e]. *)
      begin try
        let (pvars, checks, extras) = collect_for_beta ctx p e in
        (* we have a match, still need to verify validity of match *)
        Print.debug
          "Found a match of pattern@ %t@ against@ %t@, checking its \
           validity…"
          (Pattern.print_beta_hint xs h)
          (Tt.print_term xs e) ;
        begin match verify_match ~spawn:false ctx xts pvars checks with
        | None ->
          Print.debug "validity check failed";
          apply_beta hs (* not valid, try other hints *)
        | Some es ->
          (* success *)
          let e' = Tt.instantiate es 0 e' in
          let e' = List.fold_left
              (fun e ((yvs,w),es) -> Tt.mk_spine ~loc:(snd e) e yvs w es) e' extras in
          Print.debug "beta hint@ %t@ matches@ %t,@ we get@ %t"
            (Pattern.print_beta_hint xs h)
            (Tt.print_term xs e)
            (Tt.print_term xs e') ;
          whnf ctx e'
        end
      with NoMatch -> apply_beta hs (* did not match, try other hints *)
      end
  in
  if !Config.ignore_hints then e
  else begin
    let key = Pattern.term_key e in
    Print.debug "trying beta hints for@ %t" (Tt.print_term xs e);
    let e = apply_beta (Context.beta_hints key ctx) in
    Print.debug "%i found whnf@ %t )" i (Tt.print_term xs e);
    e
  end

(** Beta reduction of [Lambda (xus, (e, u))] applied to arguments [es],
    where [(yvs, t)] is the typing annotation for the application.
    Returns the resulting expression. *)
and beta_reduce ~loc ctx xus e u yvs t es =
  let rec split xuvs es' xus yvs es =
    match xus, yvs, es with
    | ([], _, _) | (_, [], []) -> xuvs, es', xus, yvs, es
    | (x,u)::xus, (_,v)::yvs, e::es -> split (xuvs @ [(x,(u,v))]) (e::es') xus yvs es
    | (_, [], _::_) | (_, _::_, []) ->
      Error.impossible ~loc "Equal.beta_reduce encountered an invalid spine"
  in
  let xuvs, es', xus, yvs, es = split [] [] xus yvs es
  in
    (* [xuvs] is a list of triples [(x,u,v)] ready to be plugged into [equal_abstraction] *)
    (* [es'] is the list of arguments that we are plugging in (reverse order from [es]) *)
    (* [xus] is the list of leftover abstraction arguments *)
    (* [yvs, es] is the list of leftover arguments *)
    (* XXX: optimization -- use the fact that one or both of [xus] and [yevs, es] are empty. *)
    let u' = Tt.mk_prod_ty ~loc xus u
    and t' = Tt.mk_prod_ty ~loc yvs t
    in
      if not (equal_abstracted_ty ctx xuvs u' t')
      then None (* The types did not match. *)
      else (* Types match -- we can reduce *)
        let xus, (e, u) =
          Tt.instantiate_abstraction
            Tt.instantiate_ty Tt.instantiate_term_ty
            es' 0 (xus, (e, u))
        and yvs, t =
          Tt.instantiate_abstraction
            Tt.instantiate_ty Tt.instantiate_ty
            es' 0 (yvs, t)
        in
        let e = Tt.mk_lambda ~loc xus e u in
        let e = Tt.mk_spine ~loc e yvs t es in
          Some e

(** Let [xuus] be the list [(x1,(u1,u1')); ...; (xn,(un,un'))] where
    [ui]  is well-formed in the context [x1:u1 , ..., x{i-1}:u{i-1} ] and
    [ui'] is well-formed in the context [x1:u1', ..., x{i-1}:u{i-1}'] and
    [v]  is well-formed in the context [x1:u1, ..., xn:un] and
    [v'] is well-formed in the context [x1:u1',..., xn:un'].
    We verify that the [ui] are equal to [ui'] and that [v] is equal to [v]. *)
and equal_abstracted_ty ctx (xuus : (Name.ident * (Pattern.pty * Tt.ty)) list) v v' =
  (* As we descend into the contexts we carry around a list of variables
     [ys] with which we unabstract the bound variables. *)
  let rec eq ys ctx =
    function
     | [] ->
        let v = Tt.unabstract_ty ys 0 v
        and v' = Tt.unabstract_ty ys 0 v'
        in equal_ty ctx v v'
     | (x,(u,u'))::xuus ->
        let u  = Tt.unabstract_ty ys 0 u
        and u' = Tt.unabstract_ty ys 0 u'
        in
          equal_ty ctx u u'
          &&
          (let y, ctx = Context.add_fresh ~loc:Location.unknown ctx x u in
             eq (ys @ [y]) ctx xuus) (* XXX optimize list append *)
   in
     eq [] ctx xuus

(** Compare two types *)
and equal_ty ctx (Tt.Ty t1) (Tt.Ty t2) = equal ctx t1 t2 Tt.typ

and equal ctx ((_,loc1) as e1) ((_,loc2) as e2) t =
  let xs = Context.used_names ctx in
  let i = cnt () in
  Print.debug "(%i checking equality of@ %t@ and@ %t@ at type@ %t" i
    (Tt.print_term xs e1)
    (Tt.print_term xs e2)
    (Tt.print_ty xs t);
  let b =
  alpha_equal e1 e2 ||
    begin (* type-directed phase *)
      let (Tt.Ty (t',_)) as t = whnf_ty ctx t in
      match t' with

        | Tt.Type ->
          equal_hints ctx e1 e2 t

        | Tt.Atom _
        | Tt.Constant _ | Tt.Spine _ ->
          (** Here we apply eta hints. *)
          begin
            let rec fold = function

              | [] ->
                (* no hints apply, proceed with applying general hints *)
                equal_hints ctx e1 e2 t

              |  ((xts, (pt, k1, k2)) as h) :: hs ->
                Print.debug "collecting for eta %t"
                  (Pattern.print_eta_hint [] h);
                begin match collect_for_eta ctx (pt, k1, k2) (t, e1, e2) with
                  | None -> fold hs (* no match, try other hints *)
                  | Some (pvars, checks) ->
                    (* check validity of the match *)
                    begin match verify_match ~spawn:true ctx xts pvars checks with
                      | Some _ -> true (* success - notice how we throw away the witness of success *)
                      | None -> fold hs (* no match on this hint, try the rest *)
                    end
                end

            in let key = Pattern.ty_key t in
            fold (if !Config.ignore_hints then []
                  else (Context.eta_hints key ctx))
          end

        | Tt.Prod (xus, u) ->
            let rec fold ctx ys es =
              begin function
              | (x, ((Tt.Ty (_, loc)) as v)) :: xvs ->
                  let v = Tt.unabstract_ty ys 0 v in
                  let y, ctx =  Context.add_fresh ~loc ctx x v in
                  let e = Tt.mk_atom ~loc y in
                  fold ctx (y :: ys) (e :: es) xvs
              | [] ->
                  let es = List.rev es in
                  let v = Tt.unabstract_ty ys 0 u
                  and e1 = Tt.mk_spine ~loc:loc1 e1 xus u es
                  and e2 = Tt.mk_spine ~loc:loc2 e2 xus u es
                  in equal ctx e1 e2 v
              end
            in fold ctx [] [] xus

        | Tt.Eq _ -> true (** Strict equality *)

        | Tt.Bracket _ -> true (** Strict bracket types *)

        | Tt.Bound _ -> Error.impossible ~loc:loc1 "deBruijn encountered in equal"

        | Tt.Lambda _ -> Error.impossible ~loc:loc1 "fun is not a type"

        | Tt.Refl _ -> Error.impossible ~loc:loc1 "refl is not a type"

        | Tt.Inhab -> Error.impossible ~loc:loc1 "[] is not a type"
    end
  in
  Print.debug "%i equality check %s)" i (if b then "succeeded" else "failed");
  b

(* Compare expressions at a given type [t] using general hints. *)
and equal_hints ctx e1 e2 t =
  (* First we normalize the expressions *)
  (* XXX can break general hints on functions. First note that when we get
     here, eta expansion has already been applied. Now h : f ≡ λx.x will fail
     because the rhs [(λx.x) y] reduces to [y] but [f y] is stuck and h won't
     apply anymore *)
  let (e1',loc1) as e1 = whnf ctx e1
  and (e2',loc2) as e2 = whnf ctx e2
  in
    (* short-circuit alpha equality *)
    alpha_equal e1 e2
    ||
    (* try general hints *)
    begin
      let key = Pattern.general_key e1 e2 t in
      Print.debug "Looking for a general hint with keys: %t" (Pattern.print_general_key key);
      List.exists
        (fun (xts, (pt, pe1, pe2) as h) ->
          Print.debug "trying general hint@ %t" (Pattern.print_hint [] h);
          match collect_for_hint ctx (pt, pe1, pe2) (t, e1, e2) with
            | None -> false
            | Some (pvars, checks) ->
              (* check validity of the match *)
              Print.debug "verifying match";
              begin match verify_match ~spawn:false ctx xts pvars checks with
                | Some _ -> true (* success - notice how we throw away the witness of success *)
                | None -> false
              end)
        (if !Config.ignore_hints then [] else Context.general_hints key ctx)
    end
    ||
    (* proceed with comparing the weak head normal forms *)
    equal_whnf ctx e1 e2

(* Compare normalized expressions. The assumption is that they both
   have a common type. *)
and equal_whnf ctx (e1',loc1) (e2',loc2) =
    (* compare reduced expressions *)
    begin match e1', e2' with

      | Tt.Atom x, Tt.Atom y -> Name.eq_atom x y

      | Tt.Bound _, _ | _, Tt.Bound _ ->
        Error.impossible ~loc:loc1 "deBruijn encountered in equal_whnf"

      | Tt.Constant (x1, es1), Tt.Constant (x2, es2) ->
        Name.eq_ident x1 x2 &&
        begin
          let yts, _ =
            begin match Context.lookup_constant x1 ctx with
            | Some ytsu -> ytsu
            | None -> Error.impossible "primitive application equality, unknown primitive operation %t" (Name.print_ident x1)
            end in
          let rec fold es' yts es1 es2 =
            match yts, es1, es2 with
            | [], [], [] -> true

            | (y,(reduce,t))::yts, e1::es1, e2::es2 ->
              (if reduce
               then equal_whnf ctx e1 e2
               else equal ctx e1 e2 (Tt.instantiate_ty es' 0 t))
              &&
              fold (e1 :: es') yts es1 es2

            | _, _, _ ->
              Error.impossible ~loc:loc1 "primitive application equality (%d, %d, %d)"
                (List.length yts)
                (List.length es1)
                (List.length es2)
          in
          fold [] yts es1 es2
        end

      | Tt.Lambda (xus, (e1, t1)), Tt.Lambda (xvs, (e2, t2)) ->
          let rec zip ys ctx = function
          | (x, u) :: xus, (_, u') :: xvs ->
              let u  = Tt.unabstract_ty ys 0 u
              and u' = Tt.unabstract_ty ys 0 u'
              in
              equal_ty ctx u u' &&
              let y, ctx = Context.add_fresh ~loc:Location.unknown ctx x u in
              zip (ys @ [y]) ctx (xus, xvs) (* XXX optimize list append *)
          | ([] as xus), xvs | xus, ([] as xvs) ->
              let t1' = Tt.mk_prod_ty ~loc:Location.unknown xus t1
              and t2' = Tt.mk_prod_ty ~loc:Location.unknown xvs t2 in
              let t1' = Tt.unabstract_ty ys 0 t1'
              and t2' = Tt.unabstract_ty ys 0 t2'
              in
              equal_ty ctx t1' t2' &&
              let e1 = Tt.mk_lambda ~loc:(snd e1) xus e1 t1
              and e2 = Tt.mk_lambda ~loc:(snd e2) xvs e2 t2
              in
              let e1 = Tt.unabstract ys 0 e1
              and e2 = Tt.unabstract ys 0 e2
              in
              equal ctx e1 e2 t1'
          in
          zip [] ctx (xus, xvs)

      | Tt.Spine (e1, xts1, es1), Tt.Spine (e2, xts2, es2) ->
          equal_spine ~loc:loc1 ctx e1 (xts1, es1) e2 (xts2, es2)

      | Tt.Type, Tt.Type -> true

      | Tt.Prod (xus, t1), Tt.Prod (xvs, t2) ->
          let rec zip xuvs = function
          | (x, u) :: xus, (_, v) :: xvs ->
            zip ((x, (u, v)) :: xuvs) (xus, xvs)
          | ([] as xus), xvs | xus, ([] as xvs) ->
              let xuvs = List.rev xuvs in
              let t1 = Tt.mk_prod_ty ~loc:loc1 xus t1
              and t2 = Tt.mk_prod_ty ~loc:loc2 xvs t2 in
              equal_abstracted_ty ctx xuvs t1 t2
          in
          zip [] (xus, xvs)

      | Tt.Eq (u, d1, d2), Tt.Eq (u', d1', d2') ->
        equal_ty ctx u u' &&
        equal ctx d1 d1' u &&
        equal ctx d2 d2' u

      | Tt.Refl (u, d), Tt.Refl (u', d') ->
        equal_ty ctx u u' &&
        equal ctx d d' u

      | Tt.Inhab, Tt.Inhab -> true

      | Tt.Bracket t1, Tt.Bracket t2 ->
        equal_ty ctx t1 t2

      | (Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Spine _ |
          Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _ | Tt.Inhab | Tt.Bracket _), _ ->
        false

    end

and equal_spine ~loc ctx e1 a1 e2 a2 =
  (* We deal with nested spines. They are nested in an inconvenient way so
     we first get them the way we need them. *)
  let rec collect_spines ab abs n ((e',_) as e) =
    match e' with
    | Tt.Spine (e, xts, es) -> collect_spines (xts,es) (ab :: abs) (n + List.length es) e
    | _ -> e, ab, abs, n
  in
  let h1, a1, as1, n1 = collect_spines a1 [] (List.length (snd a1)) e1
  and h2, a2, as2, n2 = collect_spines a2 [] (List.length (snd a2)) e2
  in
  n1 = n2 &&
  begin
    let rec fold es1 es2 ((xts1, u1), ds1) as1 ((xts2, u2), ds2) as2 =

      match (xts1, ds1), (xts2, ds2) with

      | ([], []), (xts2, ds2) ->
        begin
          match as1 with
          | [] ->
            assert (as2 = []) ;
            assert (xts2 = []) ;
            assert (ds2 = []) ;
            let u1 = Tt.instantiate_ty es1 0 u1
            and u2 = Tt.instantiate_ty es2 0 u2 in
            equal_ty ctx u1 u2 &&
            (* Compare the spine heads. We postpone doing so until
               we have checked that they have the same type, which
               we did because we compared [u1] and [u2] as well as
               the types of all the binders we encountered *)
            equal_whnf ctx h1 h2

          | ((xts1, v1), ds1) :: as1 ->
            let u1 = Tt.instantiate_ty es1 0 u1 in
            let u1' = Tt.mk_prod_ty ~loc xts1 v1 in
              if equal_ty ctx u1 u1'
              then
                 (* we may flatten spines and proceed with equality check *)
                 fold [] es2 ((xts1, v1), ds1) as1 ((xts2, u2), ds2) as2
              else
                 (* we may not flatten the spine *)
                 false (* XXX think what to do here really *)
        end

      | (((_::_) as xts1), ((_::_) as ds1)), ([], []) ->
        begin
          match as2 with
          | [] -> assert false

          | ((xts2, v2), ds2) :: as2 ->
            let u2 = Tt.instantiate_ty es2 0 u2 in
            let u2' = Tt.mk_prod_ty ~loc xts2 v2 in
              if equal_ty ctx u2 u2'
              then
                 (* we may flatten spines and proceed with equality check *)
                 fold es1 [] ((xts1, u1), ds1) as1 ((xts2, v2), ds2) as2
              else
                 (* we may not flatten the spine *)
                 false (* XXX think what to do here really *)
        end

      | ((x1,t1) :: xts1, e1::ds1), ((x2,t2)::xts2, e2::ds2) ->
        let t1 = Tt.instantiate_ty es1 0 t1
        and t2 = Tt.instantiate_ty es2 0 t2 in
        equal_ty ctx t1 t2 &&
        equal ctx e1 e2 t1 &&
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

(** [pattern_collect ctx p ?t e] matches pattern [p] against term [e]
    of possibly given type [t].

    It outputs two lists [pvars] and [checks].
    The list [pvars] maps pattern variables to the terms they were
    matched against. The list [checks] contains equalities which
    must be verified before the match is considered valid.
    It raises [NoMatch] if there is a mismatch. *)

and pattern_collect ctx p ?at_ty e =
    Print.debug "collecting %t" (Tt.print_term [] e) ;
    let e = whnf ctx e in
      pattern_collect_whnf ctx p ?at_ty e

(* Collect from [e] assuming it is in whnf. *)
and pattern_collect_whnf ctx p ?at_ty ((e', loc) as e) =
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
      | Tt.Constant (y, es) -> collect_primapp ~loc ctx x pes y es
      | _ -> raise NoMatch
    end

  | Pattern.Spine (pe, (xts, u), pes) ->
    begin match e' with
      | Tt.Spine (e, (yus, v), es) ->
        let pvars, checks, extras = pattern_collect_spine ~loc ctx (pe, (xts, u), pes) (e, (yus, v), es) in
        begin match extras with
        | _::_ ->
          Print.debug "found unexpected trailing arguments at %t"
            (Tt.print_term (Context.used_names ctx) (e', loc));
          raise NoMatch
        | [] ->
          Print.debug "no trailing arguments for %t"
            (Tt.print_term (Context.used_names ctx) (e', loc));
          pvars, checks
        end
      | _ -> raise NoMatch
    end

  | Pattern.Eq (pt, pe1, pe2) ->
    begin match e' with
      | Tt.Eq (t, e1, e2) ->
        let pvars_t, checks_t = pattern_collect_ty ctx pt t
        and pvars_e1, checks_e1 = pattern_collect ctx pe1 ~at_ty:t e1
        and pvars_e2, checks_e2 = pattern_collect ctx pe2 ~at_ty:t e2
        in pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2
      | _ -> raise NoMatch
    end

  | Pattern.Refl (pt, pe) ->
    begin match e' with
      | Tt.Refl (t, e) ->
        let pvars_t, checks_t = pattern_collect_ty ctx pt t
        and pvars_e, checks_e = pattern_collect ctx pe ~at_ty:t e
        in pvars_t @ pvars_e, checks_t @ checks_e
      | _ -> raise NoMatch
    end

  | Pattern.Bracket pt ->
    begin match e' with
      | Tt.Bracket t -> pattern_collect_ty ctx pt t
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
and pattern_collect_ty ctx (Pattern.Ty p) (Tt.Ty e) =
  pattern_collect ctx p ~at_ty:Tt.typ e

(* Collect pattern variables from a spine, and return trailing arguments.
   Also account for nested spines. *)
and pattern_collect_spine ~loc ctx (pe, xtsu, pes) (e, yvsw, es) =

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
      pattern_collect_whnf ctx ph ~at_ty:t h
    end
  in

  let rec fold xtvs es' ((xts, u), pes) pargss ((yvs, w), es) argss =
    match xts, pes, yvs, es with

    | (x,t)::xts, pe::pes, (y,v)::yvs, e::es ->
      Print.debug "collect spine (1): collect arg@ %t at %t@ from@ %t at %t"
        (Pattern.print_pattern [] ([], pe)) (Tt.print_ty [] t)
        (Tt.print_term [] e) (Tt.print_ty [] v);
      let t = Tt.instantiate_ty es' 0 t
      and v = Tt.instantiate_ty es' 0 v in
      Print.debug "collect spine (2): collect arg@ %t at %t@ from@ %t at %t"
        (Pattern.print_pattern [] ([], pe)) (Tt.print_ty [] t)
        (Tt.print_term [] e) (Tt.print_ty [] v);
      let pvars_e, checks_e = pattern_collect ctx pe ~at_ty:v e in
      let xtvs = (x,(t,v)) :: xtvs in
      let es' = e :: es' in
      let pvars, checks, extras = fold xtvs es' ((xts, u), pes) pargss ((yvs, w), es) argss in
        pvars_e @ pvars, checks_e @ checks, extras

    | ((_::_) as xts), ((_::_) as pes), [], [] ->
      begin
        match argss with
        | [] -> Error.impossible ~loc "invalid spine in pattern match (1)"
        | ((yvs, w'), es) :: argss ->
          let t1 = Tt.instantiate_ty es' 0 w
          and t2 = Tt.mk_prod_ty ~loc yvs w' in
          if not (equal_ty ctx t1 t2)
          then raise NoMatch
          else
            fold xtvs es' ((xts,u), pes) pargss ((yvs, w'), es) argss
      end

    | [], [], _::_, _::_ ->
      begin
        let xtvs = List.rev xtvs in

        let u = Tt.instantiate_ty es' 0 u
        and yvs, w = Tt.instantiate_abstraction Tt.instantiate_ty Tt.instantiate_ty es' 0 (yvs, w) in
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
        let w = Tt.instantiate_ty es' 0 w in
        let u = Tt.instantiate_ty es' 0 u in

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
and collect_for_beta ctx bp (e',loc) =
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
    let pvars, checks = collect_primapp ~loc ctx x pes y es in
    (pvars, checks, extras)

  | Pattern.BetaConstant (x, pes), Tt.Constant (y, es) ->
     let pvars, checks = collect_primapp ~loc ctx x pes y es in
     (pvars, checks, [])

  | Pattern.BetaSpine (pe, xts, pes), Tt.Spine (e, yts, es) ->
    pattern_collect_spine ~loc ctx (pe, xts, pes) (e, yts, es)

  | (Pattern.BetaAtom _ | Pattern.BetaSpine _ | Pattern.BetaConstant _), _ ->
    raise NoMatch

and collect_primapp ~loc ctx x pes y es =
  if not (Name.eq_ident x y)
  then raise NoMatch
  else begin
    let yts, _ =
      begin match Context.lookup_constant x ctx with
            | Some ytsu -> ytsu
            | None -> Error.impossible ~loc "unknown operation %t in pattern_collect" (Name.print_ident x)
      end in
    let rec fold es' yts pes es =
      match yts, pes, es with
      | [], [], [] -> [], []

      | (y,(reducing,t))::yts, pe::pes, e::es ->
         let pvars_e, checks_e =
            begin
              let t = Tt.instantiate_ty es' 0 t in
              if reducing
              then pattern_collect_whnf ctx pe ~at_ty:t e
              else pattern_collect      ctx pe ~at_ty:t e
            end in
         let pvars, checks = fold (e::es') yts pes es in
         pvars_e @ pvars, checks_e @ checks

      | _, _, _ ->
         Error.impossible ~loc "malformed primitive applications in pattern_collect"
    in
    fold [] yts pes es
  end

(** Similar to [collect_for_beta] except targeted at extracting
  values of pattern variable and residual equations in eta hints,
  where we compare a type and two terms. *)
and collect_for_eta ctx (pt, k1, k2) (t, e1, e2) =
  try
    let pvars_t,  checks_t  = pattern_collect_ty ctx pt t in
      Some ((k1,(e1,t)) :: (k2,(e2,t)) :: pvars_t, checks_t)
  with NoMatch -> None

and collect_for_hint ctx (pt, pe1, pe2) (t, e1, e2) =
  try
    let pvars_t, checks_t = pattern_collect_ty ctx pt t
    and pvars_e1, checks_e1 = pattern_collect ctx pe1 ~at_ty:t e1
    and pvars_e2, checks_e2 = pattern_collect ctx pe2 ~at_ty:t e2 in
    Some (pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2)
  with NoMatch -> None

and collect_for_inhabit ctx pt t =
  try
    let pvars_t, checks_t = pattern_collect_ty ctx pt t in
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
and verify_match ~spawn ctx xts pvars checks =
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
  let rec subst_of_pvars ctx pvars k xts es inhs =
    match xts with
    | [] -> es, inhs
    | (_,t) :: xts ->
      begin match lookup k pvars with

        | Some (e,t') ->
          (* Pattern variable [k] is matched to [e] of type [t'].
             We need to verify that [t] and [t'] are equal. *)
          let t = Tt.instantiate_ty es 0 t in
          Print.debug "matching: compare %t and %t (es %d)" (Tt.print_ty [] t) (Tt.print_ty [] t') (List.length es);
          if not (equal_ty ctx t t')
          then raise NoMatch
          else subst_of_pvars ctx pvars (k-1) xts (e :: es) inhs

        | None ->
          if not spawn
          then raise NoMatch (* we are not supposed to instantiate missing variables *)
          else begin
            (* Try to inhabit the type [t]. Actually, we first calculate the
               only possible candidate, and redo the check later when we actually
               know that the pattern match will succeed. *)
            let t = Tt.instantiate_ty es 0 t in
            Print.debug "matching: trying to inhabit@ %t" (Tt.print_ty [] t) ;
            match inhabit ~subgoals:false ctx t with
              | None -> raise NoMatch (* didn't work *)
              | Some e -> subst_of_pvars ctx pvars (k-1) xts (e :: es) ((ctx,t) :: inhs)
          end
      end
  in

  try
    (* Make a substitution from the collected [pvars] *)
    let es, inhs = subst_of_pvars ctx pvars (List.length xts - 1) xts [] [] in
    Print.debug "built substitution";
    (* Perform the equality checks to validate the match *)
    List.iter
      (function
        | CheckEqual (e1, e2, t) ->
          let e1 = Tt.instantiate es 0 e1 in
          Print.debug "CheckEqual at@ %t@ %t@ %t"
            (Tt.print_ty (Context.used_names ctx) t)
            (Tt.print_term (Context.used_names ctx) e1)
            (Tt.print_term (Context.used_names ctx) e2);
          if not (equal ctx e1 e2 t) then
            raise NoMatch

        | CheckEqualTy (xuvs, (t1, t2)) ->

          (* All de Bruijn indices refer to pvars from the point of view of
             the body, we therefore must not instantiate with
             [Tt.instantiate_abstraction] which expects them to be relative to
             the current abstraction *)
          let xuvs = List.map (fun (x, (pt, t)) -> x, (Tt.instantiate_ty es 0 pt, t)) xuvs in
          let t1', t2' =  Tt.instantiate_ty es 0 t1, t2 in

          Print.debug "es: %t"
            (Print.sequence (Tt.print_term ~max_level:0 []) "; " es);

          Print.debug "instantiated pattern return type@ %t@ as@ %t"
            (Tt.print_ty [] t1)
            (Tt.print_ty [] t1') ;

          Print.debug "instantiated rhs-term return type@ %t@ as@ %t"
            (Tt.print_ty [] t2)
            (Tt.print_ty [] t2') ;

          Print.debug "CheckEqualTy@ %t@ %t"
            (Tt.print_ty [] t1')
            (Tt.print_ty [] t2');
          if not (equal_abstracted_ty ctx xuvs t1' t2') then raise NoMatch

        | CheckAlphaEqual (e1, e2) ->
          let e1 = Tt.instantiate es 0 e1 in
          if not (alpha_equal e1 e2) then raise NoMatch)
      checks ;
    (* Perform delayed inhabitation goals *)
    (* XXX why is it safe to delay these? *)
    List.iter
      (fun (ctx, t) ->
         match inhabit ~subgoals:true ctx t with
         | None -> raise NoMatch
         | Some _ -> ())
      inhs ;
    (* match succeeded *)
    Some es
  with NoMatch -> None (* matching failed *)

and as_bracket ctx t =
  let Tt.Ty (t', loc) = whnf_ty ctx t in
  match t' with
  | Tt.Bracket t -> Some t
  | _ -> None

(** Strip brackets from a given type. *)
and strip_bracket ctx t =
  let Tt.Ty (t', loc) = whnf_ty ctx t in
  match t' with
  | Tt.Bracket t -> strip_bracket ctx t
  | _ ->  t (* XXX or should be return the whnf t? *)

(** Try to inhabit the given type [t], which must be proof-irrelevant.
    If [subgoals] is [true] then recursively resolve goals, otherwise
    just return the only possible inhabitant of [t]. *)
and inhabit ~subgoals ctx t =
  let Tt.Ty (t', loc) as t = whnf_ty ctx t in
    inhabit_whnf ~subgoals ctx t

and inhabit_whnf ~subgoals ctx ((Tt.Ty (t', loc)) as t) =
  Print.debug "trying to inhabit (subgoals = %b) whnf@ %t"
    subgoals (Tt.print_ty [] t);
  match t' with

    | Tt.Prod (xts', t') ->
      let rec fold ctx ys = function
        | [] ->
          let t' = Tt.unabstract_ty ys 0 t' in
          begin match inhabit ~subgoals ctx t' with
            | None -> None
            | Some e ->
              let e = Tt.abstract ys 0 e in
              let e = Tt.mk_lambda ~loc xts' e t' in
              Some e
          end
        | (x,t)::xts ->
          let t = Tt.unabstract_ty ys 0 t in
          let y, ctx = Context.add_fresh ~loc ctx x t in
            fold ctx (y :: ys) xts
      in
        fold ctx [] xts'

    | Tt.Eq (t, e1, e2) ->
      if not subgoals || equal ctx e1 e2 t
      then
        let e = Tt.mk_refl ~loc t e1 in
        Some e
      else None

    | Tt.Bracket t ->
      inhabit_bracket ~subgoals ~loc ctx t

    | Tt.Atom _
    | Tt.Constant _
    | Tt.Spine _
    | Tt.Bound _
    | Tt.Lambda _
    | Tt.Refl _
    | Tt.Inhab
    | Tt.Type -> None

and inhabit_bracket ~subgoals ~loc ctx t =
  if
    not subgoals ||
    begin
      (* apply inhabit hints *)
      let t = strip_bracket ctx t in
      let key = Pattern.ty_key t in
      List.exists
        (fun (xts, pt) ->
           Print.debug "attempting to inhabit@ %t using@ %t"
             (Tt.print_ty [] t)
             (Pattern.print_inhabit_hint [] (xts, pt)) ;
           match collect_for_inhabit ctx pt t with
           | None -> false
           | Some (pvars, checks) ->
             (* check validity of the match *)
             begin match verify_match ~spawn:true ctx xts pvars checks with
             | Some _ -> true
             | None -> false
             end)
        (Context.inhabit_hints key ctx)
    end
  then Some (Tt.mk_inhab ~loc)
  else None

let rec deep_prod ctx t f =
  let (Tt.Ty (t', loc)) = whnf_ty ctx t in
  match t' with

  | Tt.Prod ([], _) -> Error.impossible ~loc "empty product encountered in deep_prod"

  | Tt.Prod ((_ :: _) as xus, w) ->

     let rec fold ctx ys zvs =
       begin match zvs with
       | [] ->
          let w = Tt.unabstract_ty ys 0 w in
          let (zvs, w) = deep_prod ctx w f in
          let (zvs, w) =
            Tt.abstract_abstraction Tt.abstract_ty Tt.abstract_ty ys 0 (zvs, w) in
          (xus @ zvs, w)

       | (z,v) :: zvs ->
          let v = Tt.unabstract_ty ys 0 v in
          let y, ctx = Context.add_fresh ~loc ctx z v in
          fold ctx (y :: ys) zvs
       end in

     fold ctx [] xus

  | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Eq _ | Tt.Refl _ | Tt.Inhab
  | Tt.Bracket _ -> let t = f ctx (Tt.ty (t', loc)) in
                    ([], t)

let as_prod ctx t = deep_prod ctx t (fun ctx x -> x)

let as_universal_eq ctx ((Tt.Ty (_, loc)) as t) =
  let (xus, (Tt.Ty (t', loc) as t)) = as_prod ctx t in
  match t' with

  | Tt.Eq (t, e1, e2) ->
     (xus, (t, e1, e2))

  | Tt.Prod _ -> Error.impossible ~loc "product encountered in as_universal_eq"

  | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
  | Tt.Spine _ | Tt.Refl _ | Tt.Inhab
  | Tt.Bracket _ ->
     Error.typing ~loc
       "the type of this expression should be a universally quantified equality, found@ %t"
       (Tt.print_ty [] t)

let as_universal_bracket ctx ((Tt.Ty (_, loc)) as t) =
  deep_prod
    ctx t
    (fun ctx ((Tt.Ty (t', loc)) as t) ->
     match t' with

     | Tt.Bracket t -> strip_bracket ctx t

     | Tt.Prod _ -> Error.impossible ~loc "product encountered in as_universal_bracket"

     | Tt.Type | Tt.Atom _ | Tt.Bound _ | Tt.Constant _ | Tt.Lambda _
     | Tt.Spine _ | Tt.Refl _ | Tt.Inhab
     | Tt.Eq _ -> t)
