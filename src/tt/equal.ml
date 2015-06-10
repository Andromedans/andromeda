(** Equality checking and weak-head-normal-forms *)

(** A check is a postponed equality check.
    Pattern matching generates these. *)
type check =
  | CheckEqual of Tt.term * Tt.term * Tt.ty (* compare terms at a type *)
  | CheckEqualTy of Tt.ty * Tt.ty (* compare types *)
  | CheckAlphaEqual of Tt.term * Tt.term (* compare terms for alpha equality *)

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

    | Tt.Name x, Tt.Name y -> Name.eq x y

    | Tt.Bound i, Tt.Bound j -> i = j

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

    | (Tt.Name _ | Tt.Bound _ | Tt.Lambda _ | Tt.Spine _ |
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
          | Tt.Name _
          | Tt.Spine _
          | Tt.Type
          | Tt.Prod _
          | Tt.Eq _
          | Tt.Refl _
          | Tt.Inhab
          | Tt.Bracket _ ->
            Tt.mk_spine ~loc e xts t es
          | Tt.Bound _ ->
            Error.impossible ~loc "de Bruijn encountered in whnf"
        end
      | Tt.Lambda (_ :: _, _)
      | Tt.Prod (_ :: _, _)
      | Tt.Name _
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
  let e = weak_whnf ctx e in
  let xs = Context.used_names ctx in
  let rec apply_beta = function
    | [] -> e
    | ((_, (xts, (p, e'))) as h) :: hs ->
      (* Here we use beta hints. First we match [p] against [e]. *)
      begin match collect_for_beta ctx p e with
        | None -> apply_beta hs (* did not match, try other hints *)
        | Some (pvars, checks) ->
          (* we have a match, still need to verify validity of match *)
          begin match verify_match ~spawn:false ctx xts pvars checks with
            | None -> apply_beta hs (* not valid, try other hints *)
            | Some es ->
              (* success *)
              let e' = Tt.instantiate es 0 e' in
              Print.debug "beta hint@ %t@ matches@ %t,@ we get@ %t"
                (Pattern.print_beta_hint xs h)
                (Tt.print_term xs e)
                (Tt.print_term xs e') ;
              whnf ctx e'
          end
      end
  in
  if !Config.ignore_hints then e
  else begin
    Print.debug "trying beta hints for %t" (Tt.print_term xs e);
    apply_beta (Context.beta_hints ctx)
  end

(** Beta reduction of [Lambda (xus, (e, u))] applied to arguments [es],
    where [(yvs, t)] is the typing annotation for the application.
    Returns the resulting expression. *)
and beta_reduce ~loc ctx xus e u yvs t es =
  let rec split xuvs es' xus yvs es =
    match xus, yvs, es with
    | ([], _, _) | (_, [], []) -> xuvs, es', xus, yvs, es
    | (x,u)::xus, (_,v)::yvs, e::es -> split (xuvs @ [(x,u,v)]) (e::es') xus yvs es
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

(** Let [xuus] be the list [(x1,u1,u1'); ...; (xn,un,un')] where
    [ui]  is well-formed in the context [x1:u1 , ..., x{i-1}:u{i-1} ] and
    [ui'] is well-formed in the context [x1:u1', ..., x{i-1}:u{i-1}'] and
    [v]  is well-formed in the context [x1:u1, ..., xn:un] and
    [v'] is well-formed in the context [x1:u1',..., xn:un'].
    We verify that the [ui] are equal to [ui'] and that [v] is equal to [v]. *)
and equal_abstracted_ty ctx xuus v v' =
  (* As we descend into the contexts we carry around a list of variables
     [ys] with which we unabstract the bound variables. *)
  let rec eq ys ctx =
    function
     | [] ->
        let v = Tt.unabstract_ty ys 0 v
        and v' = Tt.unabstract_ty ys 0 v'
        in equal_ty ctx v v'
     | (x,u,u')::xuus ->
        let u  = Tt.unabstract_ty ys 0 u
        and u' = Tt.unabstract_ty ys 0 u'
        in
          equal_ty ctx u u'
          &&
          (let y, ctx = Context.add_fresh x u ctx in
             eq (ys @ [y]) ctx xuus) (* XXX optimize list append *)
   in
     eq [] ctx xuus

(** Compare two types *)
and equal_ty ctx (Tt.Ty t1) (Tt.Ty t2) = equal ctx t1 t2 Tt.typ

and equal ctx ((_,loc1) as e1) ((_,loc2) as e2) t =
 alpha_equal e1 e2 ||
    begin (* type-directed phase *)
      let (Tt.Ty (t',_)) as t = whnf_ty ctx t in
      match t' with

        | Tt.Type ->
          equal_whnf ctx e1 e2 t

        | Tt.Name _
        | Tt.Spine _ ->
          (** Here we apply eta hints. *)
          begin
            let rec fold = function

              | [] ->
                (* no hints apply, proceed with normalization phase *)
                equal_whnf ctx e1 e2 t

              |  (_, (xts, (pt, k1, k2))) :: hs ->
                begin match collect_for_eta ctx (pt, k1, k2) (t, e1, e2) with
                  | None -> fold hs (* no match, try other hints *)
                  | Some (pvars, checks) ->
                    (* check validity of the match *)
                    begin match verify_match ~spawn:true ctx xts pvars checks with
                      | Some _ -> true (* success - notice how we throw away the witness of success *)
                      | None -> fold hs (* no match on this hint, try the rest *)
                    end
                end

            in fold (if !Config.ignore_hints then [] else (Context.eta_hints ctx))
          end

        | Tt.Prod (xus, u) ->
            let rec fold ctx ys es =
              begin function
              | (x, ((Tt.Ty (_, loc)) as v)) :: xvs ->
                  let v = Tt.unabstract_ty ys 0 v in
                  let y, ctx = Context.add_fresh x v ctx in
                  let e = Tt.mk_name ~loc y in
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

and equal_whnf ctx e1 e2 t =
  let (e1',loc1) as e1 = whnf ctx e1
  and (e2',loc2) as e2 = whnf ctx e2
  in
    (* short-circuit alpha equality *)
    alpha_equal e1 e2
    ||
    (* try general hints *)
    begin
      List.exists
        (fun (_, (xts, (pt, pe1, pe2))) ->
          match collect_for_hint ctx (pt, pe1, pe2) (t, e1, e2) with
            | None -> false
            | Some (pvars, checks) ->
              (* check validity of the match *)
              (* XXX: can general hints spawn new equalities? *)
              begin match verify_match ~spawn:false ctx xts pvars checks with
                | Some _ -> true (* success - notice how we throw away the witness of success *)
                | None -> false
              end)
        (if !Config.ignore_hints then [] else Context.hints ctx)
    end
    ||
    (* compare reduced expressions *)
    begin match e1', e2' with

      | Tt.Name x, Tt.Name y -> Name.eq x y

      | Tt.Bound _, _ | _, Tt.Bound _ ->
        Error.impossible ~loc:loc1 "deBruijn encountered in equal_whnf"

      | Tt.Lambda (xus, (e1, t1)), Tt.Lambda (xvs, (e2, t2)) ->
          let rec zip ys ctx = function
          | (x, u) :: xus, (_, u') :: xvs ->
              let u  = Tt.unabstract_ty ys 0 u
              and u' = Tt.unabstract_ty ys 0 u'
              in
              equal_ty ctx u u' &&
              let y, ctx = Context.add_fresh x u ctx in
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
            zip ((x, u, v) :: xuvs) (xus, xvs)
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

      | (Tt.Name _ | Tt.Lambda _ | Tt.Spine _ |
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
            equal ctx h1 h2 u1

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
    of possibly given type [t]. It is assumed that [e] is in weak-head
    normal form.

    It outputs two lists [pvars] and [checks].
    The list [pvars] maps pattern variables to the terms they were
    matched against. The list [checks] contains equalities which
    must be verified before the match is considered valid.
    It raises [NoMatch] if there is a mismatch. *)
and pattern_collect ctx p ?at_ty e =
  (* Collect from [e] but put it in whnf first. *)
  let rec collect p ?t e =
    Print.debug "collecting %t" (Tt.print_term [] e) ;
    let e = whnf ctx e in
      collect_whnf p ?t e

  (* Colect from [e] assuming it is in whnf. *)
  and collect_whnf p ?t ((e', loc) as e) =
    match p with

    | Pattern.Name x' ->
      begin match e' with
      | Tt.Name x -> if Name.eq x' x then [], [] else raise NoMatch
      | _ -> raise NoMatch
      end

    | Pattern.PVar k ->
      begin match t with
      | Some t -> [(k, (e, t))], []
      | None ->
        (** We only get here if the caller of [pattern_collect] does not provide
            [t] _and_ we hit a variable as top-most pattern. This can happen
            if someone installed a useless beta hint, for example. So maybe
            a warning is warnted at this point. *)
        raise NoMatch
      end

    | Pattern.Spine (pe, (xts, u), pes) ->
      begin match e' with
        | Tt.Spine (e, (yus, v), es) ->
          let pvars_e, checks_e = collect pe ~t:(Tt.ty (Tt.mk_prod ~loc yus v)) e
          and pvars_es, checks_es = collect_spine ~loc xts pes es
          and t1 = Tt.mk_prod_ty ~loc xts u
          and t2 = Tt.mk_prod_ty ~loc yus v in
          pvars_e @ pvars_es,
          (CheckEqualTy (t1, t2)) :: checks_e @ checks_es
        | _ -> raise NoMatch
      end

    | Pattern.Eq (pt, pe1, pe2) ->
      begin match e' with
        | Tt.Eq (t, e1, e2) ->
          let pvars_t, checks_t = collect_ty pt t
          and pvars_e1, checks_e1 = collect pe1 e1 ~t
          and pvars_e2, checks_e2 = collect pe2 e2 ~t
          in pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2
        | _ -> raise NoMatch
      end

    | Pattern.Refl (pt, pe) ->
      begin match e' with
        | Tt.Refl (t, e) ->
          let pvars_t, checks_t = collect_ty pt t
          and pvars_e, checks_e = collect pe e ~t
          in pvars_t @ pvars_e, checks_t @ checks_e
        | _ -> raise NoMatch
      end

    | Pattern.Bracket pt ->
      begin match e' with
        | Tt.Bracket t -> collect_ty pt t
        | _ -> raise NoMatch
      end

    | Pattern.Term (e',t') ->
      begin match t with
        | Some t -> [], [CheckEqualTy (t, t'); CheckEqual (e', e, t)]
        | None ->
          (** It is unsafe to compare [e'] and [e] for equality when
              the type of [e] is not given. However, it is safe to
              compare for alpha equality. And in fact we need this
              to be able to rewrite constants (names). *)
          [], [CheckAlphaEqual (e', e)]
      end

  (* Collect from a type. *)
  and collect_ty (Pattern.Ty p) (Tt.Ty e) = collect p ~t:Tt.typ e

  (* Collect pattern variables from a spine. *)
  and collect_spine ~loc xts pes es =
    let rec fold es' xts pes es =
      match (xts, pes), es with
      | ([], []), [] -> [], []
      | ((x,t)::xts, pe::pes), e::es ->
        let pvars_e, checks_e = collect pe ~t:(Tt.instantiate_ty es' 0 t) e
        and pvars_es, checks_es = fold (e::es') xts pes es
        in pvars_e @ pvars_es, checks_e @ checks_es
      | ([],_::_), _ | ([], _), _::_ | (_::_, []), _ | (_::_, _), [] ->
        (** XXX be intelligent about differently nested but equally long spines *)
        raise NoMatch
    in
    fold [] xts pes es

  in
  collect_whnf p ?t:at_ty e

and pattern_collect_ty ctx (Pattern.Ty p) (Tt.Ty e) =
  pattern_collect ctx p ~at_ty:Tt.typ e

(** Collect values of pattern variables by matching pattern
    [p] against expression [e]. Also return the residual
    equations that remain to be checked. *)
and collect_for_beta ctx p e =
  try
    Some (pattern_collect ctx p e)
  with NoMatch -> None

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
     by the pattern match. Raise [NoMatch] if an unbound pattern
     variable is encoutered. *)
  let rec subst_of_pvars ctx pvars k xts es =
    match xts with
    | [] -> es
    | (_,t) :: xts ->
      begin match lookup k pvars with

        | Some (e,t') ->
          (* Pattern variable [k] is matched to [e] of type [t'].
             We need to verify that [t] and [t'] are equal. *)
          let t = Tt.instantiate_ty es 0 t in
          Print.debug "matching: compare %t and %t" (Tt.print_ty [] t) (Tt.print_ty [] t') ;
          if not (equal_ty ctx t t')
          then raise NoMatch
          else subst_of_pvars ctx pvars (k-1) xts (e :: es)

        | None ->
          (* Pattern variable [k] was not matched. *)
          if not spawn
          then raise NoMatch (* give up *)
          else begin
            (* Try to inhabit the type [t]. *)
            let t = Tt.instantiate_ty es 0 t in
            match inhabit ctx t with
              | None -> raise NoMatch (* didn't work *)
              | Some e -> subst_of_pvars ctx pvars (k-1) xts (e :: es)
          end
      end
  in

  try
    (* Make a substitution from the collected [pvars] *)
    let es = subst_of_pvars ctx pvars (List.length xts - 1) xts [] in
    (* Perform the equality checks to validate the match *)
    List.iter
      (function
        | CheckEqual (e1, e2, t) ->
          let e1 = Tt.instantiate es 0 e1
          and e2 = Tt.instantiate es 0 e2
          and t = Tt.instantiate_ty es 0 t in
          if not
              (equal ctx e1 e2 t) then
            raise NoMatch
        | CheckEqualTy (t1, t2) ->
          let t1 = Tt.instantiate_ty es 0 t1
          and t2 = Tt.instantiate_ty es 0 t2 in
          if not (equal_ty ctx t1 t2) then raise NoMatch
        | CheckAlphaEqual (e1, e2) ->
          let e1 = Tt.instantiate es 0 e1
          and e2 = Tt.instantiate es 0 e2 in
          if not (alpha_equal e1 e2) then raise NoMatch)
      checks ;
    (* matching succeeded *)
    Some es
  with NoMatch -> None (* matching failed *)

and as_prod ctx t =
  let Tt.Ty (t', loc) = whnf_ty ctx t in
  match t' with
  | Tt.Prod ((_ :: _, _) as a) -> Some a
  | _ -> None

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

(** Try to inhabit the given whnf type [t]. At the moment we only know how
    to inhabit universally quantified equations. In the future this could
    be a computational effect that would lead to general proof search. *)
and inhabit ctx t =
  let Tt.Ty (t', loc) as t = whnf_ty ctx t in
    inhabit_whnf ctx t

and inhabit_whnf ctx ((Tt.Ty (t', loc)) as t) =
  match t' with
    | Tt.Prod (xts', t') ->
      let rec fold ctx ys = function
        | [] ->
          let t' = Tt.unabstract_ty ys 0 t in
          begin match inhabit ctx t with
            | None -> None
            | Some e ->
              let e = Tt.abstract ys 0 e in
              let e = Tt.mk_lambda ~loc xts' e t' in
              Some e
          end
        | (x,t)::xts ->
          let t = Tt.unabstract_ty ys 0 t in
          let y, ctx = Context.add_fresh x t ctx in
            fold ctx (y :: ys) xts
      in
        fold ctx [] xts'
    | Tt.Eq (t, e1, e2) ->
      if equal ctx e1 e2 t
      then
        let e = Tt.mk_refl ~loc t e1 in
        Some e
      else None

    | Tt.Bracket t ->
      inhabit_bracket ctx t

    | Tt.Name _
    | Tt.Spine _
    | Tt.Bound _
    | Tt.Lambda _
    | Tt.Refl _
    | Tt.Inhab
    | Tt.Type -> None

and inhabit_bracket ctx t =
  let t = strip_bracket ctx t in
  (* apply inhabit hints *)
  if
    begin
    List.exists
      (fun (xts, pt) ->
        Print.debug "attempting to inhabit %t using %t"
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
      (Context.inhabit ctx)
    end
  then Some (Tt.mk_inhab ~loc:Location.unknown)
  else None

let rec as_universal_eq ctx t =
  let rec fold ctx xus ys t =
    let (Tt.Ty (t', loc)) = whnf_ty ctx t in
    match t' with

    | Tt.Prod ([], _) ->
      Error.impossible ~loc "empty product encountered in as_universal_eq"

    | Tt.Prod ((_ :: _) as zvs, w) ->
      let rec unabstract_binding ctx zs' zvs w =
      begin
        match zvs with
        | [] ->
          let w = Tt.unabstract_ty zs' 0 w in
            ctx, zs', w
        | (z,v) :: zvs ->
          let v = Tt.unabstract_ty zs' 0 v in
          let z', ctx = Context.add_fresh z v ctx in
            unabstract_binding ctx (z' :: zs') zvs w
      end
      in
        let ctx, zs', w = unabstract_binding ctx [] zvs w in
          fold ctx (xus @ zvs) (zs' @ ys) w


    | Tt.Eq (t, e1, e2) ->
      let t = Tt.abstract_ty ys 0 t
      and e1 = Tt.abstract ys 0 e1
      and e2 = Tt.abstract ys 0 e2
      in (xus, (t, e1, e2))

    | _ -> Error.typing ~loc "the type of this expression should be a universally quantified equality"
  in
  fold ctx [] [] t

(* XXX this was just copied from as_universal_eq, should refactor common code. *)
let rec as_universal_bracket ctx t =
  let rec fold ctx xus ys t =
    let (Tt.Ty (t', loc)) as t = whnf_ty ctx t in
    match t' with

    | Tt.Prod ([], _) ->
      Error.impossible ~loc "empty product encountered in as_universal_bracket"

    | Tt.Prod ((_ :: _) as zvs, w) ->
      let rec unabstract_binding ctx zs' zvs w =
      begin
        match zvs with
        | [] ->
          let w = Tt.unabstract_ty zs' 0 w in
            ctx, zs', w
        | (z,v) :: zvs ->
          let v = Tt.unabstract_ty zs' 0 v in
          let z', ctx = Context.add_fresh z v ctx in
            unabstract_binding ctx (z' :: zs') zvs w
      end
      in
        let ctx, zs', w = unabstract_binding ctx [] zvs w in
          fold ctx (xus @ zvs) (zs' @ ys) w

    | Tt.Type | Tt.Name _ | Tt.Bound _ | Tt.Lambda _ |  Tt.Spine _ | Tt.Eq _ | Tt.Refl _ |
      Tt.Inhab | Tt.Bracket _  ->
      let t = strip_bracket ctx t in
      let t = Tt.abstract_ty ys 0 t in
        (xus, t)
  in
  fold ctx [] [] t

