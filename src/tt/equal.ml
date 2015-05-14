(** Equality checking and weak-head-normal-forms *)

(** A check is a postponed equality check.
    Pattern matching generates these. *)
type check =
  | CheckEqual of Tt.term * Tt.term * Tt.ty
  | CheckEqualTy of Tt.ty * Tt.ty
  | CheckAlphaEqual of Tt.term * Tt.term

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

    | Tt.Spine (e, abs), Tt.Spine (e', abs') ->
      alpha_equal e e' &&
      alpha_equal_abstraction alpha_equal_term_ty alpha_equal_ty abs abs'

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

    | (Tt.Name _ | Tt.Bound _ | Tt.Lambda _ | Tt.Spine _ |
        Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _), _ ->
      false
  end

and alpha_equal_ty (Tt.Ty t1) (Tt.Ty t2) = alpha_equal t1 t2

and alpha_equal_term_ty (e, t) (e', t') = alpha_equal e e' && alpha_equal_ty t t'

(** Indicate a mismatch during pattern matching -- only used locally and should
    never escape [pmatch] below. *)
exception NoMatch

(** The whnf of a type [t] in context [ctx]. *)
let rec whnf_ty ctx (Tt.Ty t) =
  let t = whnf ctx t
  in Tt.ty t

(** The whnf of term [e] in context [ctx], assuming [e] has a type. *)
and whnf ctx ((e',loc) as e) =
  let e =
    begin match e' with
    | Tt.Spine (e, ([], _)) -> whnf ctx e
    | Tt.Lambda ([], (e, _)) -> whnf ctx e
    | Tt.Prod ([], Tt.Ty e) -> whnf ctx e

    | Tt.Spine (e, ((_ :: _) as xets, t)) -> whnf_spine ~loc ctx e xets t

    | Tt.Lambda (_ :: _, _)
    | Tt.Prod (_ :: _, _)
    | Tt.Name _
    | Tt.Type
    | Tt.Eq _
    | Tt.Refl _ -> e
    | Tt.Bound _ ->
       Error.impossible ~loc "de Bruijn encountered in whnf"
    end
  in
    (** Now apply beta hints *)
    e  (* XXX not yet *)


(** The whnf of a spine [Spine (e, (xets, t))] in context [ctx]. *)
and whnf_spine ~loc ctx e xets t =
  let (e',eloc) as e = whnf ctx e in
  match e' with

  | Tt.Lambda (xus, (e, u)) ->
    begin
      match beta ~loc:eloc ctx xus e u xets t with
      | None -> Tt.mk_spine ~loc e xets t
      | Some e -> whnf ctx e
    end

  | Tt.Name _
  | Tt.Spine _
  | Tt.Type
  | Tt.Prod _
  | Tt.Eq _
  | Tt.Refl _ ->
    Tt.mk_spine ~loc e xets t

  | Tt.Bound _ ->
    Error.impossible ~loc "de Bruijn encountered in whnf"

(** Beta reduction of [Lambda (xus, (e, u))] applies to arguments [yevs] at type [t].
    Returns the resulting expression. *)
and beta ~loc ctx xus e u yevs t =
  let rec split xuvs es xus yevs =
    match xus, yevs with
    | [], _ | _, [] -> xuvs, es, xus, yevs
    | (x,u)::xus, (_,(e,v))::yevs -> split (xuvs @ [(x,u,v)]) (e::es) xus yevs
  in
  let xuvs, es, xus, yevs = split [] [] xus yevs
  in
    (* [xuvs] is a list of triples [(x,u,v)] ready to be plugged into [equal_abstraction] *)
    (* [es] is the list of arguments that we are plugging in *)
    (* [xus] is the list of leftover abstraction arguments *)
    (* [yevs] is the list of leftover arguments *)
    (* XXX: optimization -- use the fact that one or both of [xus] and [yevs] are empty. *)
    let yvs = List.map (fun (y, (_, v)) -> (y,v)) yevs in
    let u' = Tt.mk_prod_ty ~loc xus u
    and t' = Tt.mk_prod_ty ~loc yvs t
    in
      if equal_abstracted_ty ctx xuvs u' t'
      then
        (* Types match -- we can reduce *)
        let xus, (e, u) =
          Tt.instantiate_abstraction
            Tt.instantiate_ty Tt.instantiate_term_ty
            es 0 (xus, (e, u))
        and yevs, t =
          Tt.instantiate_abstraction
            Tt.instantiate_term_ty Tt.instantiate_ty
            es 0 (yevs, t)
        in
        let e = Tt.mk_lambda ~loc xus e u in
        let e = Tt.mk_spine ~loc e yevs t in
          Some e
      else
        (* The types did not match. *)
        None

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
    (* xxx should check general equality hints here *)
    begin (* type-directed phase *)
      let Tt.Ty ((t',_) as t) = whnf_ty ctx t in
      match t' with

        | Tt.Type ->
          equal_whnf ctx e1 e2 t

        | Tt.Name _
        | Tt.Spine _ ->
          (** XXX first attempt to use eta hints *)
          equal_whnf ctx e1 e2 t

        | Tt.Prod (xus, u) ->
            let rec fold ctx ys xyus =
              begin function
              | (x, (Tt.Ty (_, loc) as u)) :: xus ->
                  let v = Tt.unabstract_ty ys 0 u in
                  let y, ctx = Context.add_fresh x v ctx in
                  fold ctx (ys @ [y]) (xyus @ [(x, (Tt.mk_name ~loc y, u))]) xus
              | [] ->
                  let v = Tt.unabstract_ty ys 0 u
                  and e1 = Tt.mk_spine ~loc:loc1 e1 xyus u
                  and e2 = Tt.mk_spine ~loc:loc2 e2 xyus u
                  in equal ctx e1 e2 v
              end
            in fold ctx [] [] xus

        | Tt.Eq _ -> true (** Strict equality *)

        | Tt.Bound _ -> Error.impossible ~loc:loc1 "deBruijn encountered in equal"

        | Tt.Lambda _ -> Error.impossible ~loc:loc1 "fun is not a type"

        | Tt.Refl _ -> Error.impossible ~loc:loc1 "refl is not a type"
    end

and equal_whnf ctx e1 e2 t =
  let (e1',loc1) as e1 = whnf ctx e1
  and (e2',loc2) as e2 = whnf ctx e2
  in
    alpha_equal e1 e2 ||
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

      | Tt.Spine (e1, a1), Tt.Spine (e2, a2) ->
          equal_spine ~loc:loc1 ctx e1 a1 e2 a2

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

      | (Tt.Name _ | Tt.Lambda _ | Tt.Spine _ |
          Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _), _ ->
        false

    end

and equal_spine ~loc ctx e1 a1 e2 a2 =
  (* We deal with nested spines. They are nested in an inconvenient way so
     we first get them the way we need them. *)
  let rec collect_spines ab abs n ((e',_) as e) =
    match e' with
    | Tt.Spine (e, ((xets, _) as a)) -> collect_spines a (ab :: abs) (n + List.length xets) e
    | _ -> e, ab, abs, n
  in
  let h1, a1, as1, n1 = collect_spines a1 [] (List.length (fst a1)) e1
  and h2, a2, as2, n2 = collect_spines a2 [] (List.length (fst a2)) e2
  in
  n1 = n2 &&
  begin
    let rec fold es1 es2 (xets1, u1) as1 (xets2, u2) as2 =

      match xets1, xets2 with

      | [], xets2 ->
        begin
          match as1 with
          | [] ->
            assert (as2 = []) ;
            assert (xets2 = []) ;
            let u1 = Tt.instantiate_ty es1 0 u1
            and u2 = Tt.instantiate_ty es2 0 u2 in
            equal_ty ctx u1 u2 &&
            equal ctx h1 h2 u1

          | (xets1, v1) :: as1 ->
            let u1 = Tt.instantiate_ty es1 0 u1
            and xts1 = List.map (fun (x, (_, t)) -> (x,t)) xets1 in
            let u1' = Tt.mk_prod_ty ~loc xts1 v1 in
              if equal_ty ctx u1 u1'
              then
                 (* we may flatten spines and proceed with equality check *)
                 fold [] es2 (xets1, v1) as1 (xets2, u2) as2
              else
                 (* we may not flatten the spine *)
                 false (* XXX think what to do here really *)
        end

      | (_::_) as xets1, [] ->
        begin
          match as2 with
          | [] -> assert false

          | (xets2, v2) :: as2 ->
            let u2 = Tt.instantiate_ty es2 0 u2
            and xts2 = List.map (fun (x, (_, t)) -> (x,t)) xets2 in
            let u2' = Tt.mk_prod_ty ~loc xts2 v2 in
              if equal_ty ctx u2 u2'
              then
                 (* we may flatten spines and proceed with equality check *)
                 fold es1 [] (xets1, u1) as1 (xets2, v2) as2
              else
                 (* we may not flatten the spine *)
                 false (* XXX think what to do here really *)
        end

      | (x1,(e1,t1)) :: xets1, (x2,(e2,t2))::xets2 ->
        let t1 = Tt.instantiate_ty es1 0 t1
        and t2 = Tt.instantiate_ty es2 0 t2 in
        equal_ty ctx t1 t2 &&
        equal ctx e1 e2 t1 &&
        begin
          let es1 = e1 :: es1
          and es2 = e2 :: es2
          in
            fold es1 es2 (xets1, u1) as1 (xets2, u2) as2
        end

    in
    fold [] [] a1 as1 a2 as2
  end

(** Match pattern [p] and expression [e] which has a type.
    The type may or may not be given. *)
and pmatch ctx (xts, p) ?t e =

  let rec collect p ?t e =
    match p with
    (* [PVar]s need to be tagged with a type because*)
    | Pattern.PVar k ->
      (* The type [t'] is the type given to the variable [k] in the binders
         [xts] and may be different from the type, say [t''], as a subterm in
         [p]. However, since [PVar] cannot appear under any binders, [t'] and
         [t''] are equal in the context of [xts]. Thus, we can compare
         the given type [t] to any one of them. *)
      let (x, t') =
        try (List.nth xts k) with Not_found ->
          Error.impossible
            "Encountered an unknown pattern variable in Pattern.collect" in

      begin match t with
      | Some t ->
        [(k, (e, t'))], [CheckEqualTy (t', t)]
      | None ->
        (** We only get here if the caller of [pmatch] does not provide
            [t] _and_ we hit a variable as the first pattern. This can happen
            if someone installed a useless beta hint, for example. *)
        raise NoMatch
      end

    | Pattern.Spine (pe, (pxets, u')) ->
      let loc = snd e in
      begin match as_spine ctx e with
        | Some (e, (xets, u)) ->
          let xts = List.map (fun (x, (_, t)) -> x, t) xets in
          let pvars_e, checks_e = collect pe ~t:(Tt.ty (Tt.mk_prod ~loc xts u)) e
          and pvars_xets, checks_xets = collect_spine ~loc (pxets, u') (xets, u) in
          pvars_e @ pvars_xets, checks_e @ checks_xets
        | None -> raise NoMatch
      end

    | Pattern.Eq (pt, pe1, pe2) ->
      begin match as_eq ctx e with
        | Some (t, e1, e2) ->
          let pvars_t, checks_t = collect_ty pt t
          and pvars_e1, checks_e1 = collect pe1 e1 ~t
          and pvars_e2, checks_e2 = collect pe2 e2 ~t
          in pvars_t @ pvars_e1 @ pvars_e2, checks_t @ checks_e1 @ checks_e2
        | None -> raise NoMatch
      end

    | Pattern.Refl (pt, pe) ->
      begin match as_refl ctx e with
        | Some (t, e) ->
          let pvars_t, checks_t = collect_ty pt t
          and pvars_e, checks_e = collect pe e ~t
          in pvars_t @ pvars_e, checks_t @ checks_e
        | None -> raise NoMatch
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
  and collect_ty (Pattern.Ty p) (Tt.Ty e) = collect p ~t:Tt.typ e

  and collect_spine ~loc (pxets, u') (xets, u) =
    let rec fold xts' xts es pxets xets =
      match pxets, xets with
      | [], [] ->
        let xts' = List.rev xts'
        and xts  = List.rev xts in
        let check_u = [CheckEqualTy (Tt.mk_prod_ty ~loc xts' u', Tt.mk_prod_ty ~loc xts u)]
        in [], check_u
      | (x',(pe,t'))::pxets, (x,(e,t))::xets ->
        let pvars_e, checks_e = collect pe ~t:(Tt.instantiate_ty es 0 t) e
        and pvars_xets, checks_xets = fold ((x',t)::xts') ((x,t)::xts) (e::es) pxets xets
        in pvars_e @ pvars_xets, checks_e @ checks_xets
      | ([],_::_) | (_::_,[]) ->
        (** XXX be intelligent about differently nested but equally long spines *)
        raise NoMatch
    in
    fold [] [] [] pxets xets

  in

  let rec bind_pvars ctx k pvars xts es =
    begin match pvars, xts with
      | [], [] -> ctx, es
      | (i,(e,t))::pvars, (x,t')::xts ->
        if i <> k then raise NoMatch else
          begin
            let t = Tt.instantiate_ty es 0 t in
            let ctx = Context.add_bound x (e,t) ctx in
            bind_pvars ctx (k+1) pvars xts (e::es)
          end
      | ([],_::_) | (_::_,[]) -> raise NoMatch
    end
  in

  try
    let pvars, checks = collect p ?t e in
    let pvars = List.sort (fun (i,_) (j,_) -> Pervasives.compare i j) pvars in
    let ctx, es = bind_pvars ctx 0 pvars xts [] in
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
    Some ctx
  with NoMatch -> None

and as_prod ctx t =
  let Tt.Ty (t', loc) = whnf_ty ctx t in
  match t' with
  | Tt.Prod ((_ :: _, _) as a) -> Some a
  | _ -> None

and as_spine ctx e =
  let (e', _) = whnf ctx e in
  match e' with
  | Tt.Spine (e, xets) -> Some (e, xets)
  | _ -> None

and as_eq ctx e =
  let (e', _) = whnf ctx e in
  match e' with
  | Tt.Eq (t, e1, e2) -> Some (t, e1, e2)
  | _ -> None

and as_refl ctx e =
  let (e', _) = whnf ctx e in
  match e' with
  | Tt.Refl (t, e) -> Some (t, e)
  | _ -> None

let rec as_deep_prod ctx t =
  let rec fold ctx xus ys t =
    let (Tt.Ty (t', loc)) as t = whnf_ty ctx t in
    match t' with

    | Tt.Prod ([], _) ->
      Error.impossible ~loc "empty product encountered in as_deep_prod"

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

    | _ ->
      let t = Tt.abstract_ty ys 0 t in
        (xus, t)
  in
  fold ctx [] [] t


