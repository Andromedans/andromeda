(********************)
(* Helper Functions *)
(********************)

let print_ty ctx t =
  Print.ty (Context.names ctx) t

let print_term ctx term =
  Print.term (Context.names ctx) term

let print_pattern ctx k p =
  let rec names i =
    if i < k then ("?" ^ string_of_int i) :: names (i + 1) else Context.names ctx
  in
  let rec inst i =
    if i <= k then (i, (Syntax.Var i, Position.nowhere)) :: inst (i+1) else []
  in
  let p = Pattern.shift k 0 p in
  let e = (match Pattern.subst_term (inst 0) 0 p with Pattern.Term e -> e | _ -> assert false) in
    Print.term (names 0) e

let print_pattern_ty ctx k p =
  let rec names i =
    if i < k then ("?" ^ string_of_int i) :: names (i + 1) else Context.names ctx
  in
  let rec inst i =
    if i <= k then (i, (Syntax.Var i, Position.nowhere)) :: inst (i+1) else []
  in
  let p = Pattern.shift_ty k 0 p in
  let t = (match Pattern.subst_ty (inst 0) 0 p with Pattern.Ty t -> t | _ -> assert false) in
    Print.ty (names 0) t


(** Signal that pattern matching failed. *)
exception Mismatch

(** Should we suppress failure messages? *)
let tentative = ref false

let tentatively f =
  let old = ! tentative  in
  let _ = tentative := true  in
  let answer = f()  in
  tentative := old;
  answer

(*************************)
(* Weak-Head Normalizing *)
(*************************)

let rec whnf_ty ~use_rws ctx ((t',loc) as t) =
  let whnf = whnf ~use_rws in
  let whnf_ty = whnf_ty ~use_rws in
  begin match t' with

    (* tynorm-el *)
    | Syntax.El (alpha, e) ->
      begin match fst (whnf ctx (Syntax.Universe alpha, loc) e) with

        (* tynorm-pi *)
        | Syntax.NameProd (beta, gamma, x, e1, e2)
            when Universe.eq alpha (Universe.max beta gamma) ->
          let t1 = (Syntax.El (beta, e1), snd e1) in
          let t2 = (Syntax.El (gamma, e2), snd e2) in
            Syntax.Prod (x, t1, t2),
            loc

        (* tynorm-unit *)
        | Syntax.NameUnit ->
          Syntax.Unit,
          loc

        (* tynorm-universe *)
        | Syntax.NameUniverse beta
            when Universe.eq alpha (Universe.succ beta) ->
          Syntax.Universe beta,
          loc

        (* tynorm-coerce *)
        | Syntax.Coerce (beta, gamma, e)
            when Universe.eq alpha gamma ->
          whnf_ty ctx (Syntax.El (beta, e), snd e)

        (* tynorm-paths *)
        | Syntax.NamePaths (beta, e1, e2, e3)
            when Universe.eq alpha beta ->
          let t1 = (Syntax.El (alpha, e1), snd e1) in
            Syntax.Paths (t1, e2, e3),
            loc

        (* tynorm-id *)
        | Syntax.NameId (beta, e1, e2, e3)
            when Universe.eq alpha beta ->
          let t1 = (Syntax.El (alpha, e1), snd e1) in
            Syntax.Id (t1, e2, e3),
            loc

        (* tynorm-other *)
        | (Syntax.Var _ | Syntax.Equation _ | Syntax.Rewrite _ | Syntax.Ascribe _
              | Syntax.Lambda _ | Syntax.App _ | Syntax.UnitTerm | Syntax.Idpath _
              | Syntax.J _ | Syntax.Refl _ | Syntax.Coerce _ | Syntax.NameProd _
              | Syntax.NameUniverse _ | Syntax.NamePaths _ | Syntax.NameId _) as e' ->
          Syntax.El (alpha, (e', loc)),
          loc
      end

    | (Syntax.Universe _ | Syntax.Unit | Syntax.Prod _ | Syntax.Paths _ | Syntax.Id _) ->
      t
  end

and whnf ~use_rws ctx t ((e',loc) as e0) =
  let equal_ty' = equal_ty' ~use_eqs:false ~use_rws
  and whnf = whnf ~use_rws
  in
  let e =
    begin match e' with

      (* norm-var-def *)
      | Syntax.Var k ->
        begin match Context.lookup_def k ctx with
          | None -> e0
          | Some e' -> whnf ctx t e'
        end

      (* norm-equation *)
      | Syntax.Equation (e1, t1, e2) ->
        let h = as_hint' ~use_rws ctx e1 t1 in
          whnf (Context.add_equation h ctx) t e2

      (* norm-rewrite *)
      | Syntax.Rewrite (e1, t1, e2)  ->
        let h = as_hint' ~use_rws ctx e1 t1 in
          whnf (Context.add_rewrite h ctx) t e2

      (* norm-ascribe *)
      | Syntax.Ascribe(e, _) ->
        whnf ctx t e

      | Syntax.App ((x, u1, u2), e1, e2) ->
        begin
          let e1 = whnf ctx (Syntax.Prod (x, u1, u2), loc) e1 in
            match fst e1 with
              (* norm-app-beta *)
              | Syntax.Lambda (y, t1, t2, e1')
                  when tentatively (fun () -> equal_ty' ctx u1 t1 &&
                                         equal_ty' (Context.add_var x u1 ctx) u2 t2) ->
                whnf ctx (Syntax.beta_ty u2 e2) (Syntax.beta e1' e2)

              (* norm-app-other *)
              | _ ->
                Syntax.App ((x, u1, u2), e1, e2), loc
        end

      | Syntax.J (t, (x,y,p,u), (z,e1), e2, e3, e4) ->
        begin
          let e2 = whnf ctx (Syntax.Paths (t, e3, e4), loc) e2 in
            match fst e2 with
              (* norm-J-idpath *)
              | Syntax.Idpath (t', e2')
                  when tentatively (fun () -> equal_ty' ctx t t') ->
                whnf ctx (Syntax.betas_ty u [e2; e2'; e2]) (Syntax.beta e1 e2')

              (* norm-J-other *)
              | _ ->
                Syntax.J (t, (x, y, p, u), (z, e1), e2, e3, e4), loc
        end

      (* norm-coerce-trivial *)
      | Syntax.Coerce (alpha, beta, e)
          when Universe.eq alpha beta ->
        whnf ctx (Syntax.Universe alpha, loc) e

      | Syntax.Coerce (alpha, beta, e) ->
        begin match whnf ctx (Syntax.Universe alpha, loc) e with
          (* norm-coerce-trans *)
          | (Syntax.Coerce (gamma, delta, e), _) when Universe.eq delta alpha ->
            if Universe.eq gamma beta
            then
              (* norm-coerce-trivial *)
              e
            else
              Syntax.Coerce (gamma, beta, e), loc

          (* norm-coerce-other *)
          | e ->
            Syntax.Coerce (alpha, beta, e), loc
        end

      | (Syntax.Lambda _ | Syntax.UnitTerm | Syntax.Idpath _ |
         Syntax.Refl _ | Syntax.NameUnit | Syntax.NameProd _ |
         Syntax.NameUniverse _ | Syntax.NamePaths _ | Syntax.NameId _) ->
        e0
    end
  in
    let answer =
          if use_rws
          then rewrite_term ctx e t
          else e
    in
    begin
      (*
      if (Syntax.equal answer e0) then
            Print.debug "Term %t was head-normal" (print_term ctx e0)
          else
            Print.debug "Rewrote %t to %t" (print_term ctx e0) (print_term ctx answer);
            *)
      answer
    end

(** new_match_term ctx pat e t
 *)
and new_match_term ctx inst0 k pat pat_ty term ty  =
  let tentative_equal_ty t1 t2 =
    tentatively (fun () -> equal_ty' ~use_eqs:false ~use_rws:false ctx t1 t2)  in

  (* Match a the pattern (as a spine) against the term (as a spine)
   *)
  let match_spine (pat_head, pat_args) (term_head, term_args) =
    if Pattern.eq_head tentative_equal_ty pat_head term_head then
      if List.length pat_args = List.length term_args then
        begin
         (* The two spines have equal heads and the same length *)
         Print.debug "Maybe %t@ will match %t"
            (print_pattern ctx k pat) (print_term ctx term);

         (* Loop throught the arguments and check that they correspond *)
         let rec loop pat_args term_args inst =
           match pat_args, term_args with
           | [], [] -> inst

           | ((_,pt1,_), p)::prest, ((_, t1,_), e)::erest ->
               (* XXX
                * Also need to check that the annotations on the applications
                * are equal!!! *)

               let inst =
                 try
                   Print.debug "Subpattern %t@ might match %t"
                      (print_pattern ctx k p) (print_term ctx e);
                   (* XXX This call to whnf gets rid of head beta redices in the term
                    * arguments, but also expands head definitions. That might be
                    * more than we want... *)
                   let e =  whnf ~use_rws:false ctx t1 e  in
                   new_match_term ctx inst k p pt1 e t1
                 with
                   | Mismatch ->
                       (* Try to more aggressively weak-head normalize the term
                          argument being matched, using other rewrites.
                          Note that we are reducing a *subterm* of the term
                          argument to new_match_term, so we're not going
                          into an infinite loop, at least not immediately.
                        *)
                       let e = whnf ~use_rws:true ctx t1 e in
                       new_match_term ctx inst k p pt1 e t1
               in
               let prest = Pattern.subst_pattern_args inst 0 prest  in
               loop prest erest inst
           | _, _ -> Error.impossible "match_spine/loop got lists with different lengths!"
         in let inst = loop pat_args term_args inst0 in
         inst
       end
      else
        begin
           Print.debug "Nope; lengths are different";
           raise Mismatch
        end
    else
      begin
        Print.debug "Nope; heads don't match";
        raise Mismatch
      end   in

  match pat, pat_ty with
   | Pattern.PVar i, Pattern.Ty ty' ->
       begin
         if (tentatively
               (fun () -> equal_ty' ~use_eqs:false ~use_rws:false ctx ty' ty)) then
           begin
             (* Substitutions should have gotten rid of this variable
              * if it already had a definition. *)
             assert (not (List.mem_assoc i inst0));
             (i,term) :: inst0
           end
         else raise Mismatch
       end

   | Pattern.PVar _, _ ->
       (* XXX: Unimplemented! *)
       Print.debug "XXX new_match_term: PVar without a Ty";
       raise Mismatch

   | Pattern.Term pterm, Pattern.Ty ty' when
       (* XXX Overly conservative? *)
       tentatively (fun () ->
          equal_ty' ~use_eqs:false ~use_rws:false ctx ty' ty
          && equal_term ~use_eqs:false ~use_rws:false ctx pterm term ty) ->
       inst0


   | Pattern.Term pterm, _ ->
       raise Mismatch
       (* XXX: Unsound!  *)
       (*
        when tentatively (fun () ->
          equal_term ~use_eqs:true ~use_rws:false ctx pterm term ty) ->
       Print.warning "XXX new_match_term: skipping type matching";
       inst0
       *)

   | _ ->
       begin
        (* XXX Spine creation might fail, e.g., if the
         * pattern Pe1 is a lambda
         * If so, we need to do something else.
         *)
        Print.debug "About to spine pattern %t" (print_pattern ctx k pat);
        let pat_spine =
          try Pattern.spine_of_term pat
          with e -> (Print.debug "pattern not spine-able %s"
                           (Printexc.to_string e); raise e) in

        let _ = Print.debug "About to spine term %t" (print_term ctx term) in
        let term_spine =
          try Pattern.spine_of_brazil term
          with e -> (Print.debug "term@ %t not spine-able %s"
                         (print_term ctx term) (Printexc.to_string e); raise e) in

        match_spine pat_spine term_spine
       end




(** [rewrite_term ctx e t] rewrites term [e] of type [t] using rewrite hints
    from [ctx]. After rewriting it re-runs weak head-normalization on the
    resulting term. *)

and rewrite_term ctx e t =
  Print.debug "@[<hv 4>rewrite_term %d:@ %t@]"
  (List.length (Context.rewrites ctx)) (print_term ctx e) ;

  let match_hint k pt pe1 pe2 =
        Print.debug "@[<hv 2>match_hint considering@ %t  vs@ %t at@ %t@]"
            (print_term ctx e)
            (print_pattern ctx k pe1)
            (print_pattern_ty ctx k pt) ;

    let inst = new_match_term ctx [] k pe1 pt e t  in
    let pe2 = Pattern.subst_term inst 0 pe2  in
    match pe2 with
    | Pattern.Term e2 ->
       begin
         (* XXX: This is *not* sufficient to detect uninstantiated variables;
          * only uninstantiated variables used in the right-hand-side.
          * We really need to examine the instantiation. Maybe compare
          * Length.list inst and k? *)

         (*Print.debug "Success! Hint rewrote to %t" (print_term ctx e2);*)
         e2
       end
    | _ ->
       begin
         (*Print.debug "Match succeeded, but there were uninstantiated variables";*)
         (* XXX  Per Jason, backtrack instead of failing here *)
         raise Mismatch
       end
  in
  let rec match_hints = function
    | [] ->
      e
    | (k, pt, pe1, pe2) :: hs ->
      begin try
        (*Print.debug "considering rewriting %t to %t"*)
            (*(print_pattern ctx k pe1) (print_pattern ctx k pe2);*)
        let e2 = match_hint k pt pe1 pe2 in
        Print.debug "@[<hv 2>rewrote@ %t at@ %t@;<1 -2>to@ %t@;<1 -2> using@ %t and@ %t@]"
            (print_term ctx e) (print_ty ctx t) (print_term ctx e2)
            (print_pattern ctx k pe1) (print_pattern ctx k pe2) ;
          whnf ~use_rws:true ctx t e2
        with
          | Mismatch -> match_hints hs
          | Pattern.NoSpine -> match_hints hs
          (*| Error.Error (_,s1,s2) -> (Print.debug "unexpected Error %s %s" s1 s2; match_hints hs)*)
          | ex -> (Print.debug "unexpected exception %s"
                        (Printexc.to_string ex); match_hints hs)
      end
  in
  let hs = Context.rewrites ctx in
    match_hints hs


(** See if terms [e1] and [e2] of type [t] are equal by an equality hint. *)
and equal_by_equation ctx t e1 e2 =
  Print.debug "equal_by_equation? %t@ and %t"
     (print_term ctx e1) (print_term ctx e2);
  let match_hint k pt pe1 pe2 =
    Print.debug "considering hint %t = %t"
      (print_pattern ctx k pe1) (print_pattern ctx k pe2);
    let inst = []  in
    (* Match the left-hand-side and incorporate results into the right-hand-side *)
    let inst = new_match_term ctx inst k pe1 pt e1 t  in
    let pt = Pattern.subst_ty inst 0 pt
    and pe2 = Pattern.subst_term inst 0 pe2 in

    (* Match the right-hand-side *)
    let inst = new_match_term ctx inst k pe2 pt e2 t  in

    (* Instantiate and check *)
    let pt = Pattern.subst_ty inst 0 pt
    and pe1 = Pattern.subst_term inst 0 pe1
    and pe2 = Pattern.subst_term inst 0 pe2 in
      begin match pt, pe1, pe2 with
        | Pattern.Ty t', Pattern.Term e1', Pattern.Term e2' ->
          (* Until someone proves that pattern matching works, keep the assert
             around *)
          (*assert (equal_ty' ~use_eqs:false ~use_rws:false ctx t t' &&*)
             (*equal_term ~use_eqs:false ~use_rws:false ctx e1 e1' t &&*)
             (*equal_term ~use_eqs:false ~use_rws:false ctx e2 e2' t);*)
          ()
        | _ -> raise Mismatch
      end
  in
  let rec match_hints = function
    | [] -> false
    | (k, pt, pe1, pe2) :: hs ->
      begin try
        match_hint k pt pe1 pe2 ; true
        with
          | Mismatch -> match_hints hs
          | Pattern.NoSpine -> match_hints hs
      end
  in
    match_hints (Context.equations ctx)

(* Equality of types *)
and equal_ty' ~use_rws ~use_eqs ctx t u =

  (* chk-tyeq-refl *)
  (Syntax.equal_ty t u)

  ||

  let t = whnf_ty ~use_rws ctx t  in
  let u = whnf_ty ~use_rws ctx u  in
  equal_whnf_ty ~use_eqs ~use_rws ctx t u

(* equality of weak-head-normal types *)
and equal_whnf_ty ~use_eqs ~use_rws ctx ((t', tloc) as t) ((u', uloc) as u) =
  let equal_ty' = equal_ty' ~use_eqs ~use_rws
  and equal_term = equal_term ~use_eqs ~use_rws
  in
  begin
    match t', u' with

    (* chk-tyeq-path-refl *)
    | _, _ when Syntax.equal_ty t u ->
        true

    (* chk-tyeq-prod *)
    | Syntax.Prod(x, t1, t2), Syntax.Prod(_, u1, u2) ->
        equal_ty' ctx t1 u1 &&
        equal_ty' (Context.add_var x t1 ctx) t2 u2

    (* chk-tyeq-paths *)
    | Syntax.Paths(t,e1,e2), Syntax.Paths(u,e1',e2') ->
        equal_ty' ctx t u &&
        equal_term ctx e1 e1' t &&
        equal_term ctx e2 e2' t

    (* chk-tyeq-id *)
    | Syntax.Id(t,e1,e2), Syntax.Id(u,e1',e2') ->
        equal_ty' ctx t u &&
        equal_term ctx e1 e1' t &&
        equal_term ctx e2 e2' t

    | Syntax.El _, _
    | _, Syntax.El _ ->
        begin match Syntax.name_of t, Syntax.name_of u with
          (* chk-tyeq-el *)
          | Some (e1, alpha), Some (e2, beta) ->
            Universe.eq alpha beta &&
            equal_term ctx e1 e2 (Syntax.Universe alpha, snd t)
          | (_, None) | (None, _) -> false
        end

    | (Syntax.Universe _ | Syntax.Unit
       | Syntax.Prod _ | Syntax.Paths _ | Syntax.Id _), _ ->
           (if (not (!tentative)) then
             Print.warning "@[<hv 2>Why are types@ %t@;<1 -2>and@ %t@;<1 -2>equal?@]"
                  (print_ty ctx t) (print_ty ctx u));
           false
  end

(* Equality of terms.

   Precondition: t is well-formed
                 e1 : t
                 e2 : t
 *)
and equal_term ~use_eqs ~use_rws ctx e1 e2 t =

  (*if (not (!tentative)) then*)
    Print.debug "@[<hv 4>equal_term %b %b:@ %t@;<1 -4> and@ %t@]"
          use_eqs use_rws (print_term ctx e1) (print_term ctx e2);

  (* chk-eq-refl *)
  (Syntax.equal e1 e2)

  ||

  (* chk-eq-hint *)
  (use_eqs && (equal_by_equation ctx t e1 e2 || equal_by_equation ctx t e2 e1))

  ||
  begin
    let t' = whnf_ty ~use_rws ctx t in
    equal_ext ~use_eqs ~use_rws ctx e1 e2 t'
  end


(* Equality of terms at a weak-head-normal type.

   Precondition: ty is well-formed *and weak-head-normal*
                 e1 : ty
                 e2 : ty
 *)
and equal_ext ~use_eqs ~use_rws ctx ((_, loc1) as e1) ((_, loc2) as e2) ((t', _) as t) =
  begin
    if (not (!tentative)) then
      Print.debug "@[<hv 4>equal_ext %b %b:@ %t@;<1 -4> and@ %t@ at %t@]"
            use_eqs use_rws (print_term ctx e1) (print_term ctx e2)
            (print_ty ctx t);
    match t' with

    (* chk-eq-ext-prod *)
    | Syntax.Prod (x, t, u) ->
        (* To keep the two x binders straight, we'll call the one in
           the context z. *)
        let ctx' = Context.add_var x t ctx  in   (* ctx' === ctx, z *)
                                           (* ctx       |- e1  : ... *)
        let e1' = Syntax.weaken 0 e1 in    (* ctx, z    |- e1' : ... *)
                                           (* ctx       |- e2  : ... *)
        let e2' = Syntax.weaken 0 e2 in    (* ctx, z    |- e2' : ... *)
                                           (* ctx       |- t  type *)
        let t'  = Syntax.weaken_ty 0 t in  (* ctx, z    |- t' type *)
                                           (* ctx,    x |- u  type *)
        let u' = Syntax.weaken_ty 1 u  in  (* ctx, z, x |- u' type *)
        let z = (Syntax.Var 0,
                 Position.nowhere) in      (* ctx, z    |- z : ... *)
        equal_term ~use_eqs ~use_rws ctx'
              (Syntax.App((x, t', u'), e1', z), loc1)
              (Syntax.App((x, t', u'), e2', z), loc2)
              u

    (* chk-eq-ext-unit *)
    | Syntax.Unit ->
        true

    (* chk-eq-ext-K *)
    | Syntax.Id (_, _, _) ->
        true

    (* chk-eq-ext-whnf *)
      | Syntax.Universe _ | Syntax.El _ | Syntax.Paths _ ->
        let e1' = whnf ~use_rws ctx t e1 in
        let e2' = whnf ~use_rws ctx t e2  in
        equal_whnf ~use_eqs ~use_rws ctx e1' e2' t
  end

(* Equality of two weak-head-normal terms.

   Precondition: e1 : t
                 e2 : t
 *)
and equal_whnf ~use_eqs ~use_rws ctx ((e1', loc1) as e1) ((e2', loc2) as e2) t =
  let equal_ty' = equal_ty' ~use_eqs ~use_rws
  and equal_term = equal_term ~use_eqs ~use_rws
  in
  begin
    match e1', e2' with

    (* chk-eq-whnf-reflexivity *)
    | _, _ when Syntax.equal e1 e2 ->
        true

    (* chk-eq-whnf-equation *)
    | _, _ when use_eqs && equal_by_equation ctx t e1 e2 ->
        true

    (* chk-eq-whnf-var *)
    | Syntax.Var i1, Syntax.Var i2 -> i1 = i2

    (* chk-eq-whnf-app *)
    | Syntax.App((x, t1, t2), e1, e2), Syntax.App((_, u1, u2), e1', e2') ->
        equal_ty' ctx t1 u1
        && equal_ty' (Context.add_var x t1 ctx) t2 u2
        && equal_whnf ~use_eqs ~use_rws ctx e1 e1' (Syntax.Prod (x, t1, t2), loc1)
        && equal_term ctx e2 e2' t1

    (* chk-eq-whnf-idpath *)
    | Syntax.Idpath(t, e1), Syntax.Idpath(u, e2) ->
        equal_ty' ctx t u && equal_term ctx e1 e2 t

    (* chk-eq-whnf-j *)
    | Syntax.J (t, (x,y,p,u), (z, e1), e2, e3, e4),
      Syntax.J (t', (_,_,_,u'), (_, e1'), e2', e3', e4') ->
      let ctx_xyp, ctx_z = Context.for_J t x y p z ctx in
      let e1_ty_expected =
                                                      (* ctx,    x, y, p |- u type *)
          let v = Syntax.weaken_ty 3 u                (* ctx, z, x, y, p |- v type *)
                                                      (* ctx             |- t type *)
          and s = Syntax.weaken_ty 0 t                (* ctx, z           |- s type *)
          and zvar = (Syntax.Var 0, Position.nowhere) (* ctx, z |- z *)
          in
            (* ctx, z |- v[z/x,z/y,(idpath z)/p] type *)
            Syntax.strengthen_ty v
              [zvar; zvar; (Syntax.Idpath(s, zvar), Position.nowhere)]

      in

        (*
        let j_ty_expected =
          Syntax.strengthen_ty u [e3; e4; e2]  in       (* ctx |- u[e3/x,e4/y,e2/p] *)
        *)

        equal_ty' ctx t t'
        && equal_ty' ctx_xyp u u'
        && equal_term ctx_z e1 e1' e1_ty_expected
        && equal_term ctx e3 e3' t
        && equal_term ctx e4 e4' t
        && equal_whnf ~use_eqs ~use_rws ctx e2 e2' (Syntax.Paths (t, e3, e4), loc1)

    (* chk-eq-whnf-refl *)
    | Syntax.Refl(t, e1), Syntax.Refl(u, e2) ->
        equal_ty' ctx t u && equal_term ctx e1 e2 t

    (* chk-eq-whnf-prod *)
    | Syntax.NameProd (alpha, beta, x, e1, e2),
      Syntax.NameProd (alpha', beta', _, e1', e2') ->
        Universe.eq alpha alpha' && Universe.eq beta beta'
        && equal_term ctx e1 e1' (Syntax.Universe alpha, Position.nowhere)
        && equal_term (Context.add_var x (Syntax.El(alpha,e1), Position.nowhere) ctx)
                 e2 e2' (Syntax.Universe beta, Position.nowhere)

    (* chk-eq-whnf-universe *)
    | Syntax.NameUniverse alpha, Syntax.NameUniverse beta ->
        Universe.eq alpha beta

    (* chk-eq-whnf-unit *)              (** Subsumed by reflexivity check! *)
    (*| Syntax.NameUnit, Syntax.NameUnit -> true *)

    (* chk-eq-whnf-paths *)
    | Syntax.NamePaths(alpha, e1, e2, e3), Syntax.NamePaths(alpha', e1', e2', e3') ->
        Universe.eq alpha alpha'
        && equal_term ctx e1 e1' (Syntax.Universe alpha, Position.nowhere)
        && equal_term ctx e2 e2' (Syntax.El (alpha, e1), Position.nowhere)
        && equal_term ctx e3 e3' (Syntax.El (alpha, e1), Position.nowhere)

    (* chk-eq-whnf-id *)
    | Syntax.NameId(alpha, e1, e2, e3), Syntax.NameId(alpha', e1', e2', e3') ->
        Universe.eq alpha alpha'
        && equal_term ctx e1 e1' (Syntax.Universe alpha, Position.nowhere)
        && equal_term ctx e2 e2' (Syntax.El (alpha, e1), Position.nowhere)
        && equal_term ctx e3 e3' (Syntax.El (alpha, e1), Position.nowhere)

    (* chk-eq-whnf-coerce *)
    | Syntax.Coerce(alpha, _beta, e1), Syntax.Coerce(alpha', _beta', e1') ->
        Universe.eq alpha alpha'
        && equal_term ctx e1 e1' (Syntax.Universe alpha, Position.nowhere)

    (* chk-eq-whnf-abs *)
    | Syntax.Lambda(x,t1,t2,e1), Syntax.Lambda(_,u1,u2,e2) ->
        equal_ty' ctx t1 u1
        && let ctx' = Context.add_var x t1 ctx  in
           equal_ty' ctx' t2 u2 && equal_term ctx' e1 e2 t2

    (* chk-eq-whnf-unit-right *)
    | _, Syntax.UnitTerm ->
        true

    (* chk-eq-whnf-unit-left *)
    | Syntax.UnitTerm, _ ->
        true

    (* chk-eq-whnf-refl-left *)
    | Syntax.Refl _, _ ->
        true

    (* chk-eq-whnf-refl-right *)
    | _, Syntax.Refl _ ->
        true

    | (Syntax.Var _ | Syntax.Equation _ | Syntax.Rewrite _ | Syntax.Ascribe _
      | Syntax.Lambda _ | Syntax.App _ | Syntax.Idpath _
      | Syntax.J _ | Syntax.Coerce _ | Syntax.NameUnit
      | Syntax.NameProd _ | Syntax.NameUniverse _ | Syntax.NamePaths _
      | Syntax.NameId _), _ ->
         (if (not (!tentative)) then
             Print.warning "@[<hv 2>Why are terms@ %t@;<1 -2>and@ %t@;<1 -2>equal?@]"
                  (print_term ctx e1) (print_term ctx e2));

          false
  end

and as_hint' ~use_rws ctx (_, loc) t =
  let rec collect ctx' u =
    match fst (whnf_ty ~use_rws ctx' u) with
      | Syntax.Prod (x, t1, t2) ->
        let (k, t, e1, e2) = collect (Context.add_var x t1 ctx') t2 in
          (k + 1, t, e1, e2)
      | Syntax.Id (t, e1, e2) -> (0, t, e1, e2)
      | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Paths _ ->
        Error.typing ~loc "this expression cannot be used as an equality hint, its type is %t"
          (print_ty ctx t)
  in
  let (k, t, e1, e2) = collect ctx t in
  let pt = Pattern.of_ty k t in
  let pe1 = Pattern.of_term k e1 in
  let pe2 = Pattern.of_term k e2 in
    (k, pt, pe1, pe2)

(*

(* Simple matching of a type pattern against a type. *)
and match_ty ~magenta inst l ctx pt ((t',loc) as t) =
  let match_term = match_term ~magenta
  and match_magenta = if magenta then match_ty ~magenta else (fun inst _ _ _ _ -> inst)
  and match_ty = match_ty ~magenta
  in
  match pt with

    | Pattern.Ty u  ->
      if equal_ty' ~use_eqs:false ~use_rws:false ctx t u
      then inst
      else raise Mismatch

    | Pattern.El (alpha, pe) ->
      begin match Syntax.name_of t with
        | None -> raise Mismatch
        | Some (e', beta) ->
          if Universe.eq alpha beta then
            let t = Syntax.Universe alpha, loc in
              match_term inst l ctx pe e' t
          else
            inst
      end

    | Pattern.Prod (_, pt1, pt2) ->
      begin match as_prod' ~use_rws:false ctx t with
        | None -> raise Mismatch
        | Some (x, t1, t2) ->
          let inst = match_ty inst l ctx pt1 t1 in
          let inst = match_ty inst (l+1) (Context.add_var x t1 ctx) pt2 t2 in
            inst
      end

    | Pattern.Paths (pt, pe1, pe2) ->
      begin match as_paths' ~use_rws:false ctx t with
        | None -> raise Mismatch
        | Some (t, e1, e2) ->
          let inst = match_magenta inst l ctx pt t in
          let inst = match_term inst l ctx pe1 e1 t in
          let inst = match_term inst l ctx pe2 e2 t in
            inst
      end

    | Pattern.Id (pt, pe1, pe2) ->
      begin match as_id' ~use_rws:false ctx t with
        | None -> raise Mismatch
        | Some (t, e1, e2) ->
          let inst = match_magenta inst l ctx pt t in
          let inst = match_term inst l ctx pe1 e1 t in
          let inst = match_term inst l ctx pe2 e2 t in
            inst
      end

(* Simple matching of a term pattern against a term. *)
and match_term ~magenta inst l ctx p e t =
  let match_term = match_term ~magenta
  and match_magenta = if magenta then match_ty ~magenta else (fun inst _ _ _ _ -> inst)
  and match_ty = match_ty ~magenta
  in
  match p with

  | Pattern.Term e' ->
    if equal_term ~use_eqs:false ~use_rws:true ctx e' e t
    then inst
    else raise Mismatch

  | Pattern.PVar i ->
    begin
      try
        let e' = List.assoc i inst in
        if equal_term ~use_eqs:false ~use_rws:true ctx e' e t
        then inst
        else raise Mismatch
      with
        | Not_found -> (i,e) :: inst
    end

  | Pattern.Lambda (_, pt1, pt2, pe) ->
    begin match fst (whnf ~use_rws:false ctx t e) with
      | Syntax.Lambda (x, t1, t2, e) ->
        let inst = match_ty inst l ctx pt1 t1 in
        let ctx' = Context.add_var x t1 ctx in
        let inst = match_magenta inst (l+1) ctx' pt2 t2 in
        let inst = match_term inst (l+1) ctx' pe e t2 in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.App ((_, pt1, pt2), pe1, pe2) ->
    begin match fst (whnf ~use_rws:false ctx t e) with
      | Syntax.App ((x, t1, t2), e1, e2) ->
        let inst = match_magenta inst l ctx pt1 t1 in
        let inst = match_magenta inst (l+1) (Context.add_var x t1 ctx) pt2 t2 in
        let inst = match_term inst l ctx pe1 e1 (Syntax.Prod (x, t1, t2), Position.nowhere) in
        let inst = match_term inst l ctx pe2 e2 t1 in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.Idpath (pt, pe) ->
    begin match fst (whnf ~use_rws:false ctx t e) with
      | Syntax.Idpath (t, e) ->
        let inst = match_magenta inst l ctx pt t in
        let inst = match_term inst l ctx pe e t in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.J (pt, (_,_,_,pu), (_,pe1), pe2, pe3, pe4) ->
    begin match fst (whnf ~use_rws:false ctx t e) with
      | Syntax.J (t, (x,y,p,u), (z,e1), e2, e3, e4) ->
        let inst = match_magenta inst l ctx pt t in
        let ctx_xyp, ctx_z = Context.for_J t x y p z ctx in
        let inst = match_ty inst (l+3) ctx_xyp pu u in
        let inst = match_term inst (l+1) ctx_z pe1 e1 t in
        let inst = match_term inst l ctx pe2 e2 t in
        (* XXX strictly speaking, [e3] and [e4] are magenta, so we could skip them *)
        let inst = match_term inst l ctx pe3 e3 t in
        let inst = match_term inst l ctx pe4 e4 t in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.Refl (pt, pe) ->
    begin match fst (whnf ~use_rws:false ctx t e) with
      | Syntax.Refl (t, e) ->
        let inst = match_magenta inst l ctx pt t in
        let inst = match_term inst l ctx pe e t in
          inst
      | _ -> raise Mismatch
    end

   (** XXX should switch to comparing type names *)

  | Pattern.Coerce (alpha, beta, pe) ->
    begin match fst (whnf ~use_rws:false ctx t e) with
      | Syntax.Coerce (gamma, delta, e)
          when Universe.eq alpha gamma && Universe.eq beta delta ->
        let inst = match_term inst l ctx pe e (Syntax.Universe alpha, Position.nowhere) in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.NameProd (alpha, beta, _, pe1, pe2) ->
    begin match fst (whnf ~use_rws:false ctx t e) with
      | Syntax.NameProd (gamma, delta, x, e1, e2)
          when Universe.eq alpha gamma && Universe.eq beta delta ->
        let inst = match_term inst l ctx pe1 e1 (Syntax.Universe gamma, Position.nowhere) in
        let inst =
          match_term
            inst
            (l+1)
            (Context.add_var x (Syntax.El (gamma, e1), Position.nowhere) ctx)
            pe2
            e2
            (Syntax.Universe delta, Position.nowhere)
        in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.NamePaths (alpha, pe1, pe2, pe3) ->
    begin match fst (whnf ~use_rws:false ctx t e) with
      | Syntax.NamePaths (beta, e1, e2, e3)
          when Universe.eq alpha beta ->
        let inst = match_term inst l ctx pe1 e1 (Syntax.Universe beta, Position.nowhere) in
        let inst = match_term inst l ctx pe2 e1 (Syntax.El (beta, e1), Position.nowhere) in
        let inst = match_term inst l ctx pe3 e1 (Syntax.El (beta, e1), Position.nowhere) in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.NameId (alpha, pe1, pe2, pe3) ->
    begin match fst (whnf ~use_rws:false ctx t e) with
      | Syntax.NameId (beta, e1, e2, e3)
          when Universe.eq alpha beta ->
        let inst = match_term inst l ctx pe1 e1 (Syntax.Universe beta, Position.nowhere) in
        let inst = match_term inst l ctx pe2 e1 (Syntax.El (beta, e1), Position.nowhere) in
        let inst = match_term inst l ctx pe3 e1 (Syntax.El (beta, e1), Position.nowhere) in
          inst
      | _ -> raise Mismatch
    end
*)


and as_prod' ~use_rws ctx t =
  match fst (whnf_ty ~use_rws ctx t) with

    | Syntax.Prod (x, t1, t2) ->
      Some (x, t1, t2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Paths _ | Syntax.Id _ ->
      None

and as_universe' ~use_rws ctx t =
  match fst (whnf_ty ~use_rws ctx t) with

    | Syntax.Universe alpha ->
      Some alpha

    | Syntax.El _ | Syntax.Unit | Syntax.Prod _ | Syntax.Paths _ | Syntax.Id _ ->
        None

and as_paths' ~use_rws ctx t =
  match fst (whnf_ty ~use_rws ctx t) with

    | Syntax.Paths (t, e1, e2) ->
      Some (t, e1, e2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Prod _ | Syntax.Id _ ->
      None

and as_id' ~use_rws ctx t =
  match fst (whnf_ty ~use_rws ctx t) with

    | Syntax.Id (t, e1, e2) ->
      Some (t, e1, e2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Prod _ | Syntax.Paths _ ->
      None

let equal_ty = equal_ty' ~use_eqs:true ~use_rws:true

let as_prod = as_prod' ~use_rws:true
let as_paths = as_paths' ~use_rws:true
let as_id = as_id' ~use_rws:true
let as_universe = as_universe' ~use_rws:true
let as_hint = as_hint' ~use_rws:true
