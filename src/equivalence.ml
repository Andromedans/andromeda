module type EQUIV_ARG = sig
  type term = BrazilSyntax.term

  type env
  val add_parameter     : Common.variable -> term -> env -> env
  val lookup_classifier : Common.debruijn -> env -> term
  val whnf              : env -> term -> term
  val nf                : env -> term -> term
  val print_term        : env -> term -> Format.formatter -> unit

  type handled_result
  val trivial_hr : handled_result
  val join_hr    : handled_result -> handled_result -> handled_result

  val handled : env -> term -> term -> term option -> handled_result option
  val as_whnf_for_eta : env -> term -> term * handled_result
  val as_pi   : env -> term -> term * handled_result
  val as_sigma : env -> term -> term * handled_result
  (* val as_u     : env -> term -> term  *)
end


module Make (X : EQUIV_ARG) =
  struct
    module P = BrazilPrint
    module S = BrazilSyntax

    type lazy_hr_opt = unit -> X.handled_result option

(*
 * let hr_and lhro1 lhro2 =
      match lhro1() with
        | None -> None
        | Some hr1 ->
            match lhro2() with
            | None -> None
            | Some hr2 ->  X.join_hr hr1 hr2
*)

    let rec hr_ands = function
      | [] -> Some X.trivial_hr
      | [lazy lhro] -> lhro
      | (lazy lhro) :: lhros ->
          begin
            match lhro with
            | None -> None
            | Some hr1 ->
                begin
                  match hr_ands lhros with
                  | None -> None
                  | Some hr2 ->  Some (X.join_hr hr1 hr2)
                end
          end

    let join_hr' hr1 op2 =
      match op2 with
      | Some hr2 -> Some (X.join_hr hr1 hr2)
      | None     -> None

    let join_hrs = List.fold_left X.join_hr X.trivial_hr

    (**************************)
    (* METAVARIABLE UTILITIES *)
    (**************************)

    (* Probably these should *not* be here, because
     * Brazil has no business instantiating metavariables... *)

    let patternCheck args =
      let rec loop vars_seen = function
        | [] -> Some vars_seen
        | S.Var v :: rest  when not (S.VS.mem v vars_seen) ->
            loop (S.VS.add v vars_seen) rest
        | _ -> None
      in
         loop S.VS.empty args

    let arg_map args =
      let num_args = List.length args  in
      let rec loop i = function
        | []              -> S.VM.empty
        | S.Var v :: rest ->
            let how_far_from_list_end = num_args - (i+1)  in
            S.VM.add v how_far_from_list_end (loop (i+1) rest)
        | _               -> Error.fatal "arg_map: arg is not a Var"  in
      loop 0 args

    let build_renaming args defn_free_set =
      let amap = arg_map args in      (* Map arg vars to their position *)
      S.VS.fold (fun s m -> S.VM.add s (S.VM.find s amap) m) defn_free_set S.VM.empty

    let instantiate env ((r,args) as mva) defn =
      assert (!r = None);
      (*Format.printf "instantiate: mva = %s, defn = %t@."*)
          (*(S.string_of_mva mva) (X.print_term env defn);*)
      match patternCheck args with
      | None ->
          Error.fatal "instantiate: not a pattern unification problem"
      | Some arg_var_set ->
          begin
            (* Again, to stay in the pattern fragment we need the definition's
             * free variables to be included in our argument variables.
             * We try to minimize these free variables by normalizing,
             * which might expand away definitions, etc. *)
            let defn = X.nf env defn  in
            let defn_free_set = S.free_vars defn  in
            if not (S.VS.is_empty (S.VS.diff defn_free_set arg_var_set)) then
              Error.fatal "instantiate: defn has extra free variables"
            else
              (* XXX Occurs check? *)
              (* XXX Check that all variables and metavariables in definition
               * are "older than" the * metavariable *)

              let renaming_map : Common.debruijn S.VM.t = build_renaming args defn_free_set  in
              let renamed_defn =
                S.rewrite_vars (fun c m ->
                                  if (m < c) then
                                    S.Var m
                                  else
                                    S.Var (S.VM.find (m-c) renaming_map)) defn  in
              S.set_mva mva renamed_defn;

              let _ = match S.get_mva mva with
                | Some term ->
                   (X.print_term env term);
                | None ->
                    Error.fatal "nothing found in just-set mva!"  in

              Some X.trivial_hr
          end


    (*********************)
    (* EQUALITY CHECKING *)
    (*********************)


    let rec equal env t1 t2 k =
      P.debug "equal: @[<hov>%t@ ==@ %t@ at %t@]@."
              (X.print_term env t1) (X.print_term env t2) (X.print_term env k);
      if  S.equal t1 t2  then
        (* Short-circuit in the common case *)
        Some X.trivial_hr
      else match  X.handled env t1 t2 (Some k) with
        | Some hr -> Some hr
        | None ->
            begin
              match (X.as_whnf_for_eta env k) with
              | S.Pi (x, t3, k3), hr ->
                  let env' = X.add_parameter x t3 env  in
                  let t1' = S.App (S.shift 1 t1, S.Var 0) in
                  let t2' = S.App (S.shift 1 t2, S.Var 0) in
                  let recurse = equal env' t1' t2' k3  in
                  join_hr' hr recurse
              | S.Sigma (x, c, d), hr ->
                  let t1' i = S.Proj (i, t1) in
                  let t2' i = S.Proj (i, t2) in
                  let recurse = hr_ands
                    [lazy (equal env (t1' 1) (t2' 1) c);
                     lazy (equal env (t1' 2) (t2' 2) (S.beta d (t1' 1)))]  in
                  join_hr' hr recurse
              | S.Eq(S.Ju, _, _, _), hr ->
                  (* K rule for Judgmental equality! *)
                  Some hr
              | S.Base S.TUnit, hr ->
                  (* Everything is equal at type unit *)
                  Some hr
              | _ -> equal_structural env t1 t2
          end

      (* Relies on a subsumptive universe structure, so that we can be
       * sure that if t1 : U(i) and t2 : U(j) then they both belong to
 * some common universe U(max{i,j])
 *)
and equal_at_some_universe env t1 t2 =
  P.debug "equal_at_some_universe: @[<hov>%t@ ==@ %t@]@."
      (X.print_term env t1) (X.print_term env t2);
  if  S.equal t1 t2   then
    (* Alpha-equivalent; no handlers needed *)
    Some X.trivial_hr
  else
    match  X.handled env t1 t2 None  with
    | Some hr -> Some hr
    | None    -> equal_structural env t1 t2



and equal_structural env t1 t2 =

  P.debug "equal_structural: @[<hov>%t@ ==@ %t@]@."
    (X.print_term env t1) (X.print_term env t2) ;

  let t1' = X.whnf env t1 in
  P.debug "t1' = %t@." (X.print_term env t1') ;
  let t2' = X.whnf env t2 in
  P.debug "t2' = %t@." (X.print_term env t2') ;

  if  S.equal t1' t2'  then
    (* Catches U/Var/Const/Base; also, might short-circuit *)
    Some X.trivial_hr
  else
    match  X.handled env t1' t2' None  with
    | Some hr -> Some hr
    | None ->
        match t1', t2' with
        | S.Pi    (x, t11, t12), S.Pi    (_, t21, t22)
        | S.Sigma (x, t11, t12), S.Sigma (_, t21, t22) ->
            hr_ands
            [lazy (equal_at_some_universe env                       t11 t21);
             lazy (equal_at_some_universe (X.add_parameter x t11 env) t12 t22)]

        | S.Refl(o1, t1, k1), S.Refl(o2, t2, k2) ->
            if o1 != o2  then
              None
            else hr_ands
            [ lazy (equal_at_some_universe env k1 k2);
              lazy (equal env t1 t2 k1) ]

        | S.Eq(o1, e11, e12, t1), S.Eq(o2, e21, e22, t2) ->
            if o1 != o2  then
              None
            else hr_ands
            [ lazy ( equal_at_some_universe env t1 t2 );
              lazy ( equal env e11 e21 t1 );
              lazy ( equal env e12 e22 t1 ) ]

        | S.Lambda(x, t1, e1), S.Lambda(_, t2, e2) ->
            P.warning "Why is equal_structural comparing two lambdas?";
            hr_ands
            [ lazy ( equal_at_some_universe env t1 t2 );
              lazy ( equal_structural (X.add_parameter x t1 env) e1 e2 ) ]

        | S.Pair(e11, e12), S.Pair(e21, e22) ->
            P.warning "Why is equal_structural comparing two pairs?";
            hr_ands
            [ lazy ( equal_structural env e11 e21 );
              lazy ( equal_structural env e12 e22 ) ]

        | S.Handle (e1, es1), S.Handle (e2, es2) ->
            P.warning "Why is equal_structural comparing two handles?";
            hr_ands
            ( lazy ( equal_structural env e1 e2) ::
              List.map2 (fun x y -> lazy (equal_structural env x y)) es1 es2 )

        | S.Ind_eq(o1, t1, (x,y,p,c1), (z,w1), a1, b1, q1),
          S.Ind_eq(o2, t2, (_,_,_,c2), (_,w2), a2, b2, q2) ->
            let pathtype = S.Eq(o1, a1, b1, t1) in
            let env_c = X.add_parameter p (S.shift 2 pathtype)
                           (X.add_parameter y (S.shift 1 t1)
                              (X.add_parameter x t1 env))  in
            let env_w = X.add_parameter z t1 env in

            if o1 != o2  then
              None
            else hr_ands
              [ lazy ( equal_at_some_universe env t1 t2 );
                lazy ( equal env a1 a2 t1 );
                lazy ( equal env b1 b2 t1 );

                (* OK, at this point we are confident that both paths
                   have the same type, assuming both terms are well-formed *)
                lazy ( equal env q1 q2 pathtype );

                (* We want to do eta-equivalence, but can't call "equal" because
                   we don't know the universe to compare. *)
                lazy ( equal_at_some_universe env_c c1 c2 );

                lazy ( equal env_w w1 w2
                         (S.beta (S.beta (S.beta c1 (S.Var 0))
                                         (S.Var 0))
                                 (S.Refl(o1, S.Var 0, S.shift 1 t1))) );
              ]

        | S.App _, S.App _
        | S.Proj _ , S.Proj _ ->
          begin
            match equal_path env t1' t2' with
            | Some (t,hr) ->
                P.debug "Path equivalence succeeded at type %t"
                   (X.print_term env t);
                Some hr
            | None   ->
                begin
                  P.equivalence "[Path] Why is %t == %t ?@."
                      (X.print_term env t1) (X.print_term env t2);
                   None
                end
          end

        | S.MetavarApp mva, other
        | other, S.MetavarApp mva ->
            begin
              (* We know that mva has no definition yet; otherwise
               * it would have been eliminated by whnf. *)

              (* XXX: Really need to check that other is not
               * a newer meta variable! *)

              instantiate env mva other;
            end


        | (S.Var _ | S.Lambda _ | S.Pi _ | S.App _ | S.Sigma _ |
           S.Pair _ | S.Proj _ | S.Refl _ | S.Eq _ | S.Ind_eq _ |
           S.U _ | S.Base _ | S.Const _ | S.Handle _ ), _ ->
          begin
            P.equivalence "[Mismatch] Why is %t == %t ?@."
                (X.print_term env t1) (X.print_term env t2);
            None
          end


and equal_path env e1 e2 =
  P.debug "equal_path: e1 = %t@. and e2 = %t@."
     (X.print_term env e1) (X.print_term env e2);
  match e1, e2 with
  | S.Var v1, S.Var v2 ->
      if v1 = v2 then
        Some (X.lookup_classifier v1 env, X.trivial_hr)
      else
        None


  | S.Proj (i1, e3), S.Proj (i2, e4) when i1 = i2 ->
      begin
        assert (i1 = 1 || i1 = 2);
        match equal_path env e3 e4 with
        | None -> None
        | Some (t, hr_eq) ->
            begin
              match i1, X.as_sigma env t with
              | 1, (S.Sigma(_, t1, _), hr_norm) -> Some (t1,
                                                         X.join_hr hr_eq hr_norm)
              | 2, (S.Sigma(_, _, t2), hr_norm) -> Some (S.beta t2 e1,
                                                         X.join_hr hr_eq hr_norm)
              | _, _                            ->
                  (* Should never happen, if our type checker was satisfied *)
                  P.equivalence "Why can I project from %t@ and %t@ which have type %t@ ?"
                     (X.print_term env e1) (X.print_term env e2) (X.print_term
                     env t);
                  None
            end
      end

  | S.App (e3, e5), S.App(e4, e6) ->
      begin
        match equal_path env e3 e4 with
          | Some (tfn, hr1) ->
              begin
                match X.as_pi env tfn with
                | S.Pi(_, t1, t2), hr2 ->
                  begin
                    match equal env e5 e6 t1 with
                    |  Some hr3 -> Some (S.beta t2 e5, join_hrs [hr1; hr2; hr3])
                    |  None     -> None
                  end
                | _ ->
                    (* Should never happen, if our type checker was satisfied *)
                    P.equivalence "Why do %t and %t have a pi type?"
                      (X.print_term env e3) (X.print_term env e4);
                    None
              end
          | _ -> None
      end

  | _, _ -> None

end
