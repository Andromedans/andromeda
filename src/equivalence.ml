(******************)
(* {1 Signatures} *)
(******************)

(** A list of the items needed to make the equivalence algorithm independent of
    its context (e.g., TT type checking or Brazil verification).

    Of course, it does do a lot of pattern-matching, etc., so there is a
    hard-coded assumption that we're using BrazilSyntax for the term structure.
*)
module type EQUIV_ARG = sig
  type term = BrazilSyntax.term

  type env
  val add_parameter     : Common.variable -> term -> env -> env
  val add_parameters    : (Common.variable * term) list -> env -> env
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

  val shift_to_env : (env * term) -> env -> term

  val instantiate : env -> BrazilSyntax.metavarapp
    -> term
    -> handled_result
end


(********)
(* Code *)
(********)


module Make (X : EQUIV_ARG) =
struct
  module P = BrazilPrint
  module S = BrazilSyntax

  (********************************)
  (* Handled Results and Laziness *)
  (********************************)

  (* The equivalence algorithms keep track of the handlers that they
     use to prove equivalence (direct proofs, or equivalences used to reduce
     terms to whnf), and so they must return handled_result options (to
     distinguish success from failure).

     One equivalence call might invoke quite a few recursive calls.
     Deeply-nested pattern matching quickly gets ugly, so we use a function
     hr_ands that takes the recursive calls and combines their results.

     Of course, we want to stop making recursive calls as soon as one fails
     (returns None). Therefore, we actually package the recursive calls up as
     Ocaml "lazy" thunks, and have hr_ands force each thunk in turn
     (combining handled_results as it goes) until it's done, or one thunk
     returns None.

     This would be nicer with Haskell's monads and laziness.
  *)

  (** [hr_ands lst] takes a list of [lazy] thunks returning [handled_result
      option]s. If any returns [None], the answer is [None] (and no following
      thunks are forced). If all thunks return values, they are combined into
      a single Some [handled_result].
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

  (* Map join-with-a-handled_result across an option value
  *)
  let join_hr' hr1 op2 =
    match op2 with
    | Some hr2 -> Some (X.join_hr hr1 hr2)
    | None     -> None

  (* Combine a list of handled_results
  *)
  let join_hrs = List.fold_left X.join_hr X.trivial_hr

  (*********************)
  (* EQUALITY CHECKING *)
  (*********************)

  (* The soundness equivalence relies on a number of metatheoretic
     properties. We list these here, in no particular order.

     Property REDUCE

      - If [env |- ty : U] for some universe U, then
          [env |- (X.as_pi env ty) : U] and
          [env |- ty == (X.as_pi env ty) : U].

      - If [env |- ty : U] for some universe U, then
          [env |- (X.as_sigma env ty) : U] and
          [env |- ty == (X.as_sigma env ty) : U].

      - If [env |- ty : U] for some universe U, then
          [env |- (X.as_whnf_for_eta env ty) : U] and
          [env |- ty == (X.as_whnf_for_eta env ty) : U].


      - If [env |- exp : ty] for some universe U, then
          [env |- (whnf env exp) : ty] and
          [env |- exp == (whnf env exp) : ty].



     Property HANDLED

     - If [env |- exp1: ty] and [env |- exp2 : ty] and
          [X.handled env exp1 exp2 (Some ty) <> None] then
          [env |- exp1 == exp2 : ty].

     - If [env |- exp1: ty] and [env |- exp2 : ty] and
          [X.handled env exp1 exp2 None <> None] then
          [env |- exp1 == exp2 : ty].                  <- Slightly questionable?

     Property PER

     - If [env |- exp : ty] then [env |- exp = exp : ty].
     - If [env |- exp1 == exp2 : ty] then [exp |- exp2 == exp1 : ty].
     - If [env |- exp1 == exp2 : ty] and [env |- exp2 == exp3 : ty]
         then [env |- exp1 == exp3 : ty].


     Property SUBSUMPTION

     - If [env |- exp : ty1] and [env |- ty1 == ty2 : U] for some
       universe U, then
         [env |- exp : ty2].

     - If [env |- exp1 == exp2 : ty1] and [env |- ty1 == ty2 : U] for some
       universe U, then
         [env |- exp1 == exp2 : ty2].

     Property EXTENSIONALITY

     - if [env |- exp1 : Pi x:ty1. ty2] and [env |- exp2 : Pi x:ty1. ty2]
          (so that [env, x:ty1 |- exp1 x : ty2] and [env, x:ty1 |- exp2 x : ty2])
       and [env, x:ty1 |- exp1 x == exp2 x : ty2]
       then [env |- exp1 == exp2 : Pi x:ty1. ty2].

     - if [env |- exp1 : Sigma x:ty1. ty2] and [env |- exp2 : Sigma x:ty1. ty2]
       and [env |- fst exp1 == fst exp2 : ty1]
       and [env |- snd exp1 == snd exp2 : ty2[x->fst exp1]],
       then [env |- exp1 == exp2 : Sigma x:ty1. ty2].

     - If [env |- exp1 : unit] and [env |- exp2 : unit]
       then [env |- exp1 == exp2: unit]

     - If [env |- exp1 : (exp3 == exp4 @ ty1)]
       and [env |- exp2 : (exp3 == exp4 @ ty1)]
       then [env |- exp1 == exp2 : (exp3 == exp4 @ ty1)]    <- judgmental K rule

     Property INVERSION

     - If [env |- (Pi x:ty1. ty2) : ty]
       then [env |- ty1 : U] for some universe [U] and [env, x:ty1 |- ty2 : U].

     - If [env |- (Sigma x:ty1. ty2) : ty]
       then [env |- ty1 : U] for some universe [U] and [env, x:ty1 |- ty2 : U].

     - If [env |- Refl(o,exp1,ty2) : ty]
       then [env |- ty2 : U] for some universe [U] and [env |- exp1 : ty2].

     - If [env |- Eq(o, exp1, exp2, ty3) : ty]
       then [env |- ty3 : U] for some universe [U]
       and [env |- exp1 : ty3] and [env |- exp2 : ty3].

     - If [env |- Lambda(x, ty1, ty2, exp3) : ty]
       then [env |- ty1 : U] and [env, x:ty1 |- ty2 : U] for some universe [U],
       and [env, x:ty1 |- exp3 : ty2].

     - If [env |- Pair(exp1, exp2, x, ty1, ty2) : ty]
       then [env |- ty1 : U] and [env, x:ty1 |- ty2 : U] for some universe [U],
       and [env |- exp1 : ty1] and [env |- exp2 : ty2{x->exp1}].

     - If [env |- Ind_eq(o, t, (x,y,p,c), (z,w), a, b, q) : ty]
       then [env |- t : U_i] where (if o = Pr then U_i is fibered)
       and  [env |- a : t] and [env |- b : t],
       and  [env |- Id(o,a,b,t) : U_i] and [env |- q : Id(o,a,b,t)],
       and  [env, x:t, y:t, p:Id(o,x,y,t) |- c : U_j]
                 where if (o = Pr then U_j is fibered)
       and  [env, z:t |- w : c{x,y,z->z,z,Refl(o,z,t)}].

    Property SUBST

     - If [env1, x:ty1, env2 |- exp : ty]
       and [env |- exp1 : ty1]
       then [env1, env2[x->exp1] |- exp[x->exp1] : ty[x->exp1]]

    Property WEAKENING

    - If [env1, env2 |- exp : ty]
      and [env1 |- ty1 : U] for some universe [U],
      and x not in dom(env1,env2),
      then [env1, x:ty1, env2 |- exp: ty]

    Property VALIDITY

    - If [env |- exp : ty]
      then [env |- ty : U] for some universe [U].

    - If [env |- exp1 == exp2 : ty]
      then [env |- exp1 : ty] and [env |- exp2 : ty].


    Property FUNCTIONALITY

     - If [env1, x:ty1, env2 |- exp : ty2]
       and [env1 |- exp1 == exp2 : ty1],
       then [env1, env2{x->exp1} |- exp[x->exp1] == exp[x->exp2] : ty[x->exp1]]

    PROPERTY FUNCTIONALITY2

    - If [env1, x:ty1, env2 |- exp3 == exp4 : ty2]
      and [env1 |- exp1 == exp2 : ty1],
      then [env1, env2{x->exp1} |- exp3{x->exp1} == exp4{exp->exp2} : ty{x->exp1}]

    Property EQUIV

     - If [env1, x:ty1, env2 |- ...] for any judgment
       and [env1 |- ty1 == ty2 : U] for some universe [U],
       then [env1, x:ty2, env2 |- ...].

    Property JOIN

     - If [env1 |- ty1 : U1] and [env2 |- ty2 : U2] for universes [U1] and [U2],
       then [env1 |- ty1 : U] and [env2 |- ty2 : U] for some common universe [U].


  *)

  (* If the inputs satisfy the preconditions [env |- ty : U] for some universe
     [U], [env |- exp1 : ty], and [env |- exp2 : ty], then
     [equal env exp1 exp2 ty] tries to decide whether [env |- exp1 == exp2 : ty]
     is provable.

     Returns [None] if no proof is found. Returns [Some hr] if there is a
     proof, where [hr] records the handlers that were used for the proof.

     In the absence of handlers and judgmental-equivalence types, the algorithm
     reduces to a standard (sound and complete) algorithm.

     In the presence of handlers and judgmental-equivalence types, the
     algorithm is surely not complete (unless enough handlers are provided)
     and might even be non-terminating.

     Our hope is that it remains sound.
  *)

  let rec equal env exp1 exp2 ty =
    P.debug "equal: @[<hov>%t@ ==@ %t@ at %t@]@."
      (X.print_term env exp1) (X.print_term env exp2) (X.print_term env ty);

    if  S.equal exp1 exp2  then

      (* Success by REFLEXIVITY *)
      Some X.trivial_hr

    else match  X.handled env exp1 exp2 (Some ty) with

      | Some hr ->
        (* Success by HANDLED *)
        Some hr

      | None ->
        begin
          let reduced_ty = X.as_whnf_for_eta env ty in

          (* By REDUCE,
             [env |- reduced_ty : U] and
             [env |- ty == reduced_ty : U]
           *)

          match reduced_ty with

          | S.Pi (x, ty1, ty2), hr_whnf ->

            (* By SUBSUMPTION, we know that
               [env |- exp1 : Pi x:ty1. ty2] and
               [env |- exp2 : Pi x:ty1. ty2] and
               [env |- exp1 == exp2 : Pi x:ty1. ty2]
             *)

            (*
               By TYPING (including WEAKENING), we know that
                 [env, x:ty1 |- exp1 x : ty2] and
                 [env, x:ty1 |- exp2 x : ty2].
               Construct these two applications, indexed appropriately
             *)
            let env'  = X.add_parameter x ty1 env  in
            let exp1' = X.shift_to_env (env, exp1) env'  in
            let exp2' = X.shift_to_env (env, exp2) env'  in
            let app1  = S.App (exp1', S.Var 0) in
            let app2  = S.App (exp2', S.Var 0) in

            (*
               Since [env |- (Pi x:ty1. ty2) : U], by INVERSION we have
                [env |- ty1 : U] and [env, x:ty1 |- ty2 : U].

               By PER, SUBSUMPTION, and EXTENSIONALITY,
                [env |- exp1 == exp2 : ty]
                   if
                [env |- exp1 == exp2 : Pi x:ty1. ty2]
                   if
                [env, x:ty1 |- exp1' x == exp2' x : ty2]

               So that's what we check.
            *)
            let hr_recurse = equal env' app1 app2 ty2  in

            (* Report all handlers used *)
            join_hr' hr_whnf hr_recurse

          | S.Sigma (x, ty1, ty2), hr_whnf ->

            (* By SUBSUMPTION, we know that
               [env |- exp1 : Sigma x:ty1. ty2] and
               [env |- exp2 : Sigma x:ty1. ty2].

               By TYPING, then,
               [env |- fst exp1 : ty1]
               [env |- fst exp2 : ty1]
               [env |- snd exp1 : ty2[x->fst exp1]]
               [env |- snd exp2 : ty2[x->fst exp2]]
             *)
            let fst_exp1 = S.Proj(1, exp1)  in
            let fst_exp2 = S.Proj(1, exp2)  in
            let snd_exp1 = S.Proj(2, exp1)  in
            let snd_exp2 = S.Proj(2, exp2)  in

            (*
                By PER, SUBSUMPTION, and EXTENSIONALITY,
                [env |- exp1 == exp2 : ty]
                   if
                [env |- exp1 == exp2 : Sigma x:ty1. ty2]
                   if
                ( [env |- fst exp1 == fst exp2 : ty1]
                  and
                  [env |- snd exp1 == snd exp2 : ty2[x->fst exp1]] )

                So that's what we check.
             *)
            let hr_recurse = hr_ands
                [lazy (equal env fst_exp1 fst_exp2 ty1);
                 (* If we get this far, we know that
                     [env |- fst exp1 == fst exp2 : ty1].
                    Since we already know that
                     [env |- Sigma x:ty1. ty2 : U],
                    by INVERSION we get
                     [env, x:ty1 |- ty2 : U].
                    By FUNCTIONALITY, then,
                     [env |- ty2[x->fst exp1] == ty2[x->fst exp2] : U],
                    so by PER and SUBSUMPTION we have
                     [env |- snd exp2 : ty2[x->fst exp1]]
                  *)
                 lazy (equal env snd_exp1 snd_exp2 (S.beta ty2 fst_exp1))]  in

            (* Report all handlers used *)
            join_hr' hr_whnf hr_recurse

          | S.Eq(S.Ju, _, _, _), hr_whnf ->

            (* By EXTENSIONALITY, a.k.a. the K rule for judgmental equality. *)
            Some hr_whnf

          | S.Base S.TUnit, hr_whnf ->

            (* By EXTENSIONALITY, a.k.a. everything is equal at type unit *)
            Some hr_whnf

          | _ ->

            (* We failed to prove that the comparison type [ty] is
               equivalent to a type where extensionality applies (either
               because it isn't, or because we didn't have the right handlers
               in place). So, we invoke a helper function that computes
               weak-head-normal forms and does mostly structural comparison.
             *)
            equal_whnfs env exp1 exp2

        end

  (* Assuming that [env |- ty1 : U] and [env |- ty2 : U] for some
     universe [U], try to prove that [env |- ty1 == ty2 : U]. If we fail (because
     they're not judgmentally equivalent, or we don't have enough handlers
     installed) return None. Otherwise return [Some hr] where [hr] records all
     handlers used in the equivalence proof.

     XXX: We have not have proved it at universe U, but rather at some
     *arbitrary* universe they happen to have in common!
   *)
  and equal_at_some_universe env ty1 ty2 =
    begin
      P.debug "equal_at_some_universe: @[<hov>%t@ ==@ %t@]@."
        (X.print_term env ty1) (X.print_term env ty2);

      if  S.equal ty1 ty2   then

        (* Alpha-equivalent; by PER, no handlers needed *)
        Some X.trivial_hr

      else
        (* See if there's an applicable handler *)
        match  X.handled env ty1 ty2 None  with
        | Some hr ->
            (* Success by HANDLED *)
            Some hr
        | None    ->
            (* Otherwise, try comparing their whnfs *)
            equal_whnfs env ty1 ty2
    end

  (* Assuming that [exp1] and [exp2] are terms (possibly types, possibly not)
     satisfying [env |- exp1 : ty] and [env |- exp2 : ty] for some (unspecified)
     common type [ty], try to prove that [env |- exp1 == exp2 : ty] by reducing each
     to a weak-head-normal form, and comparing the two terms using congruence
     rules (i.e., without any top-level use of extensionality).

     If we fail (because they're not judgmentally equivalent, or we don't have
     enough handlers installed) return None. Otherwise return [Some hr] where
     [hr] records all handlers used in the equivalence proof.

     WARNING: equal_whnfs does *not* check for alpha-equivalence or a suitable
     handler before it reduces the two inputs to weak-head-normal form; it
     assumes the caller has checked that already. Thus, equal_whnf should
     not call itself directly because we might miss an alpha-equivalence
     or (more likely) a suitable handler.
  *)
  and equal_whnfs env exp1 exp2 =

    P.debug "equal_whnfs: @[<hov>%t@ ==@ %t@]@."
      (X.print_term env exp1) (X.print_term env exp2) ;

    (* Compute weak-head-normal forms.*)

    let exp1' = X.whnf env exp1 in
    P.debug "exp1' = %t@." (X.print_term env exp1') ;

    let exp2' = X.whnf env exp2 in
    P.debug "exp2' = %t@." (X.print_term env exp2') ;

    (* By REDUCE, we know that
         [G |- exp1' : ty] and [G |- ty2' : ty]
       and more importantly that
         [G |- exp1 == exp1' : ty] and [G |- exp2 == exp2' : ty].
     *)

    if  S.equal exp1' exp2'  then

      (* Note: this check is not just an optimization, but also covers
         the cases where both sides are U/Var/Const/Base. *)

      (* Success by PER *)
      Some X.trivial_hr

    else

      (* Maybe there's an applicable handler? *)
      match  X.handled env exp1' exp2' None  with

      | Some hr ->
          (* Success by HANDLED *)
          Some hr

      | None ->
          begin
            match exp1', exp2' with

            | S.Pi    (x, ty11, ty12), S.Pi    (_, ty21, ty22)
            | S.Sigma (x, ty11, ty12), S.Sigma (_, ty21, ty22) ->
              let env' = X.add_parameter x ty11 env  in
              hr_ands
                [ (* By INVERSION,
                       [env |- ty11 : U1] and [env |- ty21 : U2]
                     By JOIN,
                       [env |- ty11 : U] and [env |- ty21 : U].
                   *)
                  lazy (equal_at_some_universe env ty11 ty21);

                 (* By INVERSION,
                       [env, x:ty11 |- ty12 : U1]
                       [env, x:ty21 |- ty22 : U2].
                    By EQUIV,
                       [env, x:ty11 |- ty22 : U2]
                    By JOIN,
                       [env, x:ty11 |- ty12 : U']
                       [env, x:ty11 |- ty22 : U']
                    Note that env' := env, x:ty11.
                  *)
                 lazy (equal_at_some_universe env' ty12 ty22)]

            | S.Refl(o1, exp1, ty1), S.Refl(o2, exp2, ty2) ->
              if o1 <> o2  then
                None
              else hr_ands
                  [ (* By INVERSION,
                         [env |- ty1 : U1] and [env |- ty2 : U2]
                         [env |- exp1 : ty1] and [env |- exp2 : ty2]
                       By JOIN,
                         [env |- ty1 : U] and [env |- ty2 :U] for some [U].
                     *)
                    lazy (equal_at_some_universe env ty1 ty2);

                    (* By PER and SUBSUMPTION,
                         [env |- exp2 : ty1].
                     *)
                    lazy (equal env exp1 exp2 ty1) ]

            | S.Eq(o1, exp11, exp12, ty1), S.Eq(o2, exp21, exp22, ty2) ->
              if o1 <> o2  then
                None
              else hr_ands
                  [ (* By INVERSION,
                         [env |- ty1 : U1] and [env |- ty2 : U2], so
                       so by JOIN we have
                         [env |_ ty1 : U] and [env |- ty2 : U].
                    *)
                    lazy ( equal_at_some_universe env ty1 ty2 );

                    (* By INVERSION,
                         [env |- exp11 : ty1] and [env |- exp21 : ty2]
                       so by PER and SUBSUMPTION
                         [env |- exp21 : ty1].
                     *)
                    lazy ( equal env exp11 exp21 ty1 );

                    (* By INVERSION,
                         [env |- exp12 : ty1] and [env |- exp22 : ty2]
                       so by PER and SUBSUMPTION
                         [env |- exp22 : ty1].
                     *)
                    lazy ( equal env exp12 exp22 ty1 ) ]

            | S.Lambda(x, t11, t12, e1), S.Lambda(_, t21, t22, e2) ->
              P.warning "Why is equal_whnfs comparing two lambdas?";
              let env' = X.add_parameter x t11 env  in
              hr_ands
                [ (* By INVERSION,
                      [env |- t11 : U1] and [env |- t21 : U2]
                     By JOIN,
                      [env |- t11 : U] and [env |- t21 : U]
                   *)
                  lazy ( equal_at_some_universe env t11 t21 );

                  (* By INVERSION,
                       [env, x:t11 |- t12 : U1] and [env, x:t21 |- t22 : U2].
                     By JOIN,
                       [env, x:t11 |- t12 : U] and [env, x:t21 |- t22 : U].
                     By EQUIV,
                       [env, x:t11 |- t22 : U].
                     Note that env' := env, x:t11.
                   *)
                  lazy ( equal_at_some_universe env' t12 t22 );

                  (* By INVERSION,
                       [env, x:t11 |- e1 : t12] and [env, x:t21 |- e2 : t22].
                     By EQUIV,
                       [env, x:t11 |- e2 : t22].
                     By PER and SUBSUMPTION,
                       [env, x:t11 |- e2 : t12].
                   *)
                  lazy ( equal env' e1 e2 t12) ]

            | S.Pair(e11, e12, x1, t11, t12), S.Pair(e21, e22, _, t21, t22) ->
              (* This case is unlikely to occur, unless we managed to
                 avoid eta-equivalence in the equals function. *)
              hr_ands
                [ (* By INVERSION,
                       [env |- t11 : U1] and [env |- t21 : U2],
                     so by JOIN,
                       [env |- t11 : U] and [env |- t21 : U].
                   *)
                  lazy ( equal_at_some_universe env t11 t21 );

                  (* By INVERSION and JOIN,
                       [env, x:t11 |- t12 : U] and [env, x:t21 |- t22 : U].
                     By EQUIV,
                       [env, x:t11 |- t22 : U]
                   *)
                  lazy ( equal_at_some_universe (X.add_parameter x1 t11 env) t12 t22 );

                  (* By INVERSION,
                       [env |- e11 : t11] and [env |- e21 : t21].
                     By PER and SUBSUMPTION,
                       [env |- e21 : t11].
                   *)
                  lazy ( equal env e11 e21 t11 );

                  (* By INVERSION,
                       [env |- e12 : t12{x->e11}]
                       [env |- e22 : t22{x->e21}].
                     By FUNCTIONALITY,
                       [env |- t22{x->e11} == t22{x->e21} : U].
                     By SUBST,
                       [env |- t12{x->e11} == t22{x->e11} : U].
                     By PER and SUBSUMPTION,
                       [env |= e22 : t12{x->e11}].
                   *)
                  lazy ( equal env e12 e22 (S.beta t12 e11)) ]

            | S.Handle _, _
            | _, S.Handle _ ->
                Error.impossible "equal_whnfs: whnf didn't eliminate Handle"


            | S.Ind_eq(S.Ju, _, _, _, _, _, _), _
            | _, S.Ind_eq(S.Ju, _, _, _, _, _, _) ->
                Error.impossible "equal_whnfs: whnf didn't eliminate Ind_eq(Ju"

            | S.MetavarApp _, _
            | _, S.MetavarApp _
            | S.App _, S.App _
            | S.Proj _ , S.Proj _
            | S.Ind_eq(S.Pr, _, _, _, _, _, _),
                S.Ind_eq(S.Pr, _, _, _, _, _, _) ->
              begin
                match equal_path env exp1' exp2' with
                | Some (t,hr) ->
                  P.debug "Path equivalence succeeded at type %t"
                    (X.print_term env t);
                  Some hr
                | None   ->
                  begin
                    (* XXX: This will be a problem if we ever speculatively
                     * try to invoke equivalences. Better to return the
                     * message as a string... *)
                    P.equivalence "@[<hov>[Path] Why is %t ==@ %t ?@]@."
                      (X.print_term env exp1') (X.print_term env exp2');
                    None
                  end
              end

            | (S.Var _ | S.Lambda _ | S.Pi _ | S.App _ | S.Sigma _ |
               S.Pair _ | S.Proj _ | S.Refl _ | S.Eq _ | S.Ind_eq _ |
               S.U _ | S.Base _ | S.Const _ ), _ ->
              begin
                (* XXX: This will be a problem if we ever speculatively
                 * try to invoke equivalences... *)
                P.equivalence "[Mismatch] Why is %t == %t ?@."
                  (X.print_term env exp1') (X.print_term env exp2');
                None
              end
          end

  (* [equal_path] assumes inputs are already in whnf! *)

  (* XXX: To get metavariables to work properly, we may need to put this
   * into spine form... *)

  (* XXX: If M is a metavariable, we know how to deal with
   *           M x y z = f(x,y,z).
   *      What about
   *           ((M x).1) y z = f(x,y,z) ?
   *)

  and equal_path env e1 e2 =
    P.debug "equal_path: e1 = %t@. and e2 = %t@."
      (X.print_term env e1) (X.print_term env e2);
    match e1, e2 with
    | S.Var v1, S.Var v2 ->
      if v1 = v2 then
        Some (X.lookup_classifier v1 env, X.trivial_hr)
      else
        None

    | S.MetavarApp mva1, S.MetavarApp mva2 when S.equal e1 e2 ->
      Some (mva1.S.mv_ty, X.trivial_hr)

    | S.MetavarApp mva, other
    | other, S.MetavarApp mva ->
      begin

        (* We know that mva has no definition yet; otherwise
         * it would have been eliminated by whnf. Further,
         * it can't be two of the same metavariables, because
         * then alpha-equivalence would have short-circuited. *)

        (* XXX Need to do further checks, e.g., occurs *)
        let hr = X.instantiate env mva other in
        Some (mva.S.mv_ty, hr)
      end

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
              P.equivalence "Why do %t and %t have a Pi type?"
                (X.print_term env e3) (X.print_term env e4);
              None
          end
        | _ -> None
      end

    | S.Ind_eq(o1, t1, (x,y,p,c1), (z,w1), a1, b1, q1),
      S.Ind_eq(o2, t2, (_,_,_,c2), (_,w2), a2, b2, q2) ->

        assert (o1 = S.Pr && o2 = S.Pr); (* Otherwise not in whnf *)

        let (env_xyp, env_z) =
          S.create_ind_eq_envs X.add_parameters env S.Pr t1 (x,y,p) z  in

        let w1_ty, lhs_type =
          S.create_ind_eq_types env_xyp env_z S.Pr t1 (x,y,p,c1) z a1 b1 q1  in

        let hr_eq_opt = hr_ands

            [ (* By INVERSION and JOIN,
                   [env |- t1 : Uf_i] and [env |- t2 : Uf_i].
               *)
              lazy ( equal_at_some_universe env t1 t2 );

              (* Now
                   [env |- t1 == t2 : Uf'_i].

                 By INVERSION,
                   [env |- a1 : t1] and [env |- a2 : t2].
                 By PER and SUBSUMPTION,
                   [env |- a2 : t1].
               *)
              lazy ( equal env a1 a2 t1 );

              (* Now
                   [env |- a1 == a2 : t1].

                 By INVERSION,
                   [env |- b1 : t1] and [env |- b2 : t2].
                 By PER and SUBSUMPTION,
                   [env |- b2 : t1].
               *)
              lazy ( equal env b1 b2 t1 );

              (* Now
                   [env |- b1 == b2 : t1].

                 By INVERSION,
                   [env |- q1 : (a1 = b1 @ t1)] and
                   [env |- q2 : (a2 = b2 @ t2)].
                 By CONGRUENCE,
                   [env |- (a1 = b1 @ t1) == (a2 = b2 @ t2) : Uf_i].
                 By PER and SUBSUMPTION,
                   [env |- q2 : (a1 = b1 @ t1)].
               *)
              lazy ( equal env q1 q2 (S.Eq(o1,a1,b1,t1)) );

              (* Now
                   [env |- e1 == e2 : (a1 = b1 @ t1)].

                 By INVERSION and JOIN,
                   [env, x:t1, y:t1, p:(x = y @ t1) |- c1 : Uf_j]
                   [env, x:t2, y:t2, p:(x = y @ t2) |- c2 : Uf_j]
                 By SUBST and WEAKENING,
                   [env, x:t1, y:t1, p:(x = y @ t1) |- c2 : Uf_j].
                 We call this last environment env_c.
               *)
              lazy ( equal_at_some_universe env_xyp c1 c2 );


              (* Now [env, x:t1, y:t1, p:(x = y @ t1) |- c1 == c2 : Uf_j'].
                 where [c1] and [c2] both belong to [Uf_j'] in that environment.

                 By INVERSION,
                   [env, z:t1 |- w1 : c1{x,y,p->z,z,idpath(z,t1)}]
                 and we call this last type w1_ty.
                 By INVERSION,
                   [env, z:t2 |- w2 : c2{x,y,p->z,z,idpath(z,t2)}]
                 By EQUIV,
                   [env, z:t1 |- w2 : c2{x,y,p->z,z,idpath(z,t2)}]

                 By WEAKENING,
                   [env, z:t1, x:t1, y:t1, p:(x = y @ t1) |- c2 : U_j']
                 Since by RULE
                   [env, z:t1 |- z : t1]
                 By SUBST,
                   [env, z:t1, y:t1, p:(z = y @ t1) |- c2{x->z} : U_j']
                 and again by SUBST
                   [env, z:t1, p:(z = z @ t1) |- c2{x,y->z,z} : U_j']
                 (We can turn the iterated substitution into a parallel
                 substitution because y is not free in z.)
                 By RULES we have
                   [env, z:t1 |- (z = z @ t1) == (z = z @ t2) : U_i']
                 So by RULE and CONGRUENCE
                   [env, z:t1 |- idpath(z,t1) == idpath(z,t2) : (z = z @ t1)
                 By FUNCTIONALITY,
                   [env, z:t1 |- c2{x,y,p->z,z,idpath(z,t1)} ==
                                    c2{x,y,p->z,z,idpath(z,t2)} : U_j']
                 By PER and SUBSUMPTION,
                   [env, z:t1 |- w2 : c2{x,y,p->z,z,idpath(z,t1)}].
               *)
              lazy ( equal env_z w1 w2 w1_ty );

              (* Now
                   [env, z:t1 |- w1 == w2 : c2{x,y,p->z,z,idpath(z,t1)}]
              *)
            ]  in

        begin
          match hr_eq_opt with
          | Some hr_eq -> Some (lhs_type, hr_eq)
          | None -> None
        end


    | _, _ -> None

end
