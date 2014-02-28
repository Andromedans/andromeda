module type EQUIV_ARG = sig
  type term = BrazilSyntax.term

  type env
  val add_parameter     : Common.variable -> term -> env -> env
  val lookup_classifier : Common.debruijn -> env -> term
  val whnf              : env -> term -> term
  val print_term        : env -> term -> Format.formatter -> unit

  type handled_result
  val trivial_hr : handled_result
  val join_hr    : handled_result -> handled_result -> handled_result

  val handled : env -> term -> term -> term option -> handled_result option
  val as_whnf_for_eta : env -> term -> term
  val as_pi   : env -> term -> term
  val as_sigma : env -> term -> term
  (* val as_u     : env -> term -> term  *)
end


module Make (X : EQUIV_ARG) =
  struct
    module D = BrazilInput
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

    let rec equal env t1 t2 k =
      P.debug "equal: %t == %t at %t@."
              (X.print_term env t1) (X.print_term env t2) (X.print_term env k);
      if  S.equal t1 t2  then
        (* Short-circuit in the common case *)
        Some X.trivial_hr
      else match  X.handled env t1 t2 (Some k) with
        | Some hr -> Some hr
        | None ->
            begin
              match (X.as_whnf_for_eta env k) with
              | S.Pi (x, t3, k3) ->
                  let env' = X.add_parameter x t3 env  in
                  let t1' = S.App (S.shift 1 t1, S.Var 0) in
                  let t2' = S.App (S.shift 1 t2, S.Var 0) in
                  equal env' t1' t2'  k3
              | S.Sigma (x, c, d) ->
                  let t1' i = S.Proj (i, t1) in
                  let t2' i = S.Proj (i, t2) in
                  hr_ands
                    [lazy (equal env (t1' 1) (t2' 1) c);
                     lazy (equal env (t1' 2) (t2' 2) (S.beta d (t1' 1)))]
              | S.Eq(S.Ju, _, _, _) ->
                  (* K rule for Judgmental equality! *)
                  Some X.trivial_hr
              | S.Base S.TUnit ->
                  (* Everything is equal at type unit *)
                  Some X.trivial_hr
              | _ -> equal_structural env t1 t2
          end

      (* Relies on a subsumptive universe structure, so that we can be
       * sure that if t1 : U(i) and t2 : U(j) then they both belong to
 * some common universe U(max{i,j])
 *)
and equal_at_some_universe env t1 t2 =
  P.debug "equal_at_some_universe: %t == %t@."
      (X.print_term env t1) (X.print_term env t2);
  if  S.equal t1 t2   then
    Some X.trivial_hr
  else
    match  X.handled env t1 t2 None  with
    | Some hr -> Some hr
    | None    -> equal_structural env t1 t2



and equal_structural env t1 t2 =

  P.debug "equal_structural: %t == %t@." (X.print_term env t1) (X.print_term env t2) ;

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
             lazy (P.debug "halfway through Pi/Sigma@."; Some X.trivial_hr);
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

            (*
  | S.J(o1, c1, w1, a1, b1, t1, p1),
    S.J(o2, c2, w2, a2, b2, t2, p2) ->
      let pathtype = S.Eq(o1, a1, b1, t1) in
      o1 == o2 &&
      equal_at_some_universe env t1 t2 &&
      equal env a1 a2 t1 &&
      equal env b1 b2 t1 &&
      (* OK, at this point we are confident that both paths
       * have the same type *)
      equal env p1 p2 pathtype &&
      equal_at_some_universe
           (X.add_parameter "_p" pathtype
              (X.add_parameter "_y" t1
                (X.add_parameter "_x" t1 env))) c1 c2   &&
      equal (X.add_parameter "_z" t1 env) w1 w2
               (S.beta (S.beta (S.beta w1 (S.Var 0)) (S.Var 0))
                       (S.Refl(o1, S.Var 0, t1)))
                       *)

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

        | (S.Var _ | S.Lambda _ | S.Pi _ | S.App _ | S.Sigma _ |
           S.Pair _ | S.Proj _ | S.Refl _ | S.Eq _ | S.J _ |
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
        (* XXX: Should use as_sigma here! *)
        match i1, equal_path env e3 e4 with
          | 1, Some (S.Sigma(_, t1, _), hr) -> Some (t1, hr)
          | 2, Some (S.Sigma(_, _, t2), hr) -> Some (S.beta t2 e1, hr)
          | _                               -> None
      end

  | S.App (e3, e5), S.App(e4, e6) ->
      begin
        match equal_path env e3 e4 with
          | Some (tfn, hr1) ->
              begin
                match X.as_pi env tfn with
                | S.Pi(_, t1, t2) ->
                  begin
                    match equal env e5 e6 t1 with
                    |  Some hr2 -> Some (S.beta t2 e5, X.join_hr hr1 hr2)
                    |  None     -> None
                  end
                | _ ->
                    P.equivalence "Why do %t and %t have a pi type?"
                      (X.print_term env e3) (X.print_term env e4);
                    None
              end
          | _ -> None
      end

  | _, _ -> None

end
