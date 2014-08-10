(********************)
(* Helper Functions *)
(********************)


let print_ty ctx t =
  Print.ty (Context.names ctx) t

let print_term ctx term =
  Print.term (Context.names ctx) term

(* It's important to eta-expand the next two functions, because they're
 * expensive, and we don't want to do all the administrative computation
 * if debugging output has been disabled (so that this function will never
 * be applied to a ppf argument).
 *)

let print_pattern ctx k p ppf =
  let rec names i =
    if i < k then ("?" ^ string_of_int i) :: names (i + 1) else Context.names ctx
  in
  let rec inst i =
    if i <= k then (i, Syntax.mkVar i) :: inst (i+1) else []
  in
  let p = Pattern.shift k 0 p in
  let e = (match Pattern.subst_term (inst 0) 0 p with Pattern.Term e -> e | _ -> assert false) in
    Print.term (names 0) e ppf

let print_pattern_ty ctx k p ppf =
  let rec names i =
    if i < k then ("?" ^ string_of_int i) :: names (i + 1) else Context.names ctx
  in
  let rec inst i =
    if i <= k then (i, Syntax.mkVar i) :: inst (i+1) else []
  in
  let p = Pattern.shift_ty k 0 p in
  let t = (match Pattern.subst_ty (inst 0) 0 p with Pattern.Ty t -> t | _ -> assert false) in
    Print.ty (names 0) t ppf

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




(***********)
(* type_of *)
(***********)

let rec type_of ctx (exp, loc') =
  let loc = Position.nowhere in
  match exp with

  | Syntax.Var v -> Context.lookup_var v ctx

  | Syntax.Equation (_, _, body)

  | Syntax.Rewrite (_, _, body) -> type_of ctx body

  | Syntax.Ascribe (_, ty) -> ty

  | Syntax.Lambda (x, t1, t2, _) -> Syntax.Prod(x, t1, t2), loc

  | Syntax.App ((_, _, t2), _, e2) -> Syntax.beta_ty t2 e2

  | Syntax.Spine (f, fty, es) ->
      type_of ctx (Syntax.from_spine ~loc:loc' f fty es)

  | Syntax.Record lst ->
    Syntax.RecordTy (List.map (fun (lbl, (x, t, _)) -> (lbl, (x, t))) lst), loc

  | Syntax.Project (_, lst, lbl) ->
    let rec fold = function
      | [] -> Error.impossible ~loc:loc' "Equal.type_of: invalid label in projection"
      | (lbl',(_,t)) :: lst ->
        if lbl = lbl' then t else fold lst
    in
      fold lst

  | Syntax.UnitTerm -> Syntax.Unit, loc

  | Syntax.Idpath (t, e) -> Syntax.Paths(t, e, e), loc

  | Syntax.J (_, (_, _, _, u), _, e2, e3, e4) -> Syntax.strengthen_ty u [e2; e3; e4]

  | Syntax.Refl (t, e) -> Syntax.Id(t, e, e), loc

  | Syntax.Coerce (_, beta, _) -> Syntax.Universe beta, loc

  | Syntax.NameRecordTy lst ->
    Syntax.Universe (Universe.maxs (List.map (fun (_,(_,u,_)) -> u) lst)), loc

  | Syntax.NameUnit -> Syntax.Universe Universe.zero, loc

  | Syntax.NameProd (alpha, beta, _, _, _) -> Syntax.Universe (Universe.max alpha beta), loc

  | Syntax.NameUniverse alpha -> Syntax.Universe (Universe.succ alpha), loc

  | Syntax.NamePaths (alpha, _, _, _)

  | Syntax.NameId    (alpha, _, _, _) -> Syntax.Universe alpha, loc


(*************************)
(* Weak-Head Normalizing *)
(*************************)

let rec whnf_ty ~use_rws ctx ((t',loc) as t) =
  let whnf = whnf ~use_rws in
  let whnf_ty = whnf_ty ~use_rws in
  begin match t' with

    (* tynorm-el *)
    | Syntax.El (alpha, e) ->
      begin match fst (whnf ctx (Syntax.mkUniverse ~loc alpha) e) with

        (* tynorm-pi *)
        | Syntax.NameProd (beta, gamma, x, e1, e2)
            when Universe.eq alpha (Universe.max beta gamma) ->
          let t1 = Syntax.mkEl ~loc:(snd e1) beta e1 in
          let t2 = Syntax.mkEl ~loc:(snd e2) gamma e2 in
          Syntax.mkProd ~loc x t1 t2

        (* tynorm-unit *)
        | Syntax.NameUnit ->
          Syntax.mkUnit ~loc ()

        | Syntax.NameRecordTy lst
            when Universe.eq alpha (Universe.maxs (List.map (fun (_,(_,u,_)) -> u) lst)) ->
          Syntax.mkRecordTy ~loc
            (List.map
               (fun (lbl, (x, beta, e)) -> (lbl, (x, Syntax.mkEl ~loc:(snd e) beta e)))
               lst)

        (* tynorm-universe *)
        | Syntax.NameUniverse beta
            when Universe.eq alpha (Universe.succ beta) ->
          Syntax.mkUniverse ~loc beta

        (* tynorm-coerce *)
        | Syntax.Coerce (beta, gamma, e)
            when Universe.eq alpha gamma ->
          whnf_ty ctx (Syntax.mkEl ~loc:(snd e) beta e)

        (* tynorm-paths *)
        | Syntax.NamePaths (beta, e1, e2, e3)
            when Universe.eq alpha beta ->
          let t1 = Syntax.mkEl ~loc:(snd e1) alpha e1  in
            Syntax.mkPaths ~loc t1 e2 e3

        (* tynorm-id *)
        | Syntax.NameId (beta, e1, e2, e3)
            when Universe.eq alpha beta ->
          let t1 = Syntax.mkEl ~loc:(snd e1) alpha e1  in
            Syntax.mkId ~loc t1 e2 e3

        (* tynorm-other *)
        | (Syntax.Var _ | Syntax.Equation _ | Syntax.Rewrite _ | Syntax.Ascribe _
              | Syntax.Lambda _ | Syntax.App _ | Syntax.Spine _
              | Syntax.Record _ | Syntax.Project _
              | Syntax.UnitTerm | Syntax.Idpath _ | Syntax.NameRecordTy _
              | Syntax.J _ | Syntax.Refl _ | Syntax.Coerce _ | Syntax.NameProd _
              | Syntax.NameUniverse _ | Syntax.NamePaths _ | Syntax.NameId _) as e' ->
          Syntax.mkEl ~loc alpha (e', loc)
      end

    | (Syntax.Universe _ | Syntax.RecordTy _ | Syntax.Unit |
       Syntax.Prod _ | Syntax.Paths _ | Syntax.Id _) ->
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
          let e1 = whnf ctx (Syntax.mkProd ~loc x u1 u2) e1 in
            match fst e1 with
              (* norm-app-beta *)
              | Syntax.Lambda (y, t1, t2, e1')
                  when tentatively (fun () -> equal_ty' ctx u1 t1 &&
                                         equal_ty' (Context.add_var x u1 ctx) u2 t2) ->
                whnf ctx (Syntax.beta_ty u2 e2) (Syntax.beta e1' e2)

              (* norm-app-other *)
              | _ ->
                Syntax.mkApp ~loc x u1 u2 e1 e2
        end

      | Syntax.Spine (f, fty, es) ->
          begin
            (* match Context.lookup_def f ctx with
            | None -> e0
            | Some _ -> *) whnf ctx t (Syntax.from_spine f fty es)
          end

      | Syntax.Project (e, lst, lbl) ->
        begin
          let e' = whnf ctx (Syntax.mkRecordTy lst) e in
            match fst e' with
              | Syntax.Record lst'
                when (equal_ty' ctx (type_of ctx e') (Syntax.mkRecordTy lst)) ->
                let rec fold es = function
                  | [] -> Error.impossible "Equal.whnf: invalid projection during whnf"
                  | (lbl',(_,_,e)) :: lst ->
                    if lbl = lbl'
                    then
                      List.fold_left Syntax.beta e es
                    else
                      fold (e::es) lst
                in
                  fold [] lst'
              | _ ->
                Syntax.mkProject e' lst lbl
        end

      | Syntax.J (t, (x,y,p,u), (z,e1), e2, e3, e4) ->
        begin
          let e2 = whnf ctx (Syntax.mkPaths ~loc t e3 e4) e2 in
            match fst e2 with
              (* norm-J-idpath *)
              | Syntax.Idpath (t', e2')
                  when tentatively (fun () -> equal_ty' ctx t t') ->
                whnf ctx (Syntax.betas_ty u [e2; e2'; e2]) (Syntax.beta e1 e2')

              (* norm-J-other *)
              | _ ->
                Syntax.mkJ ~loc t (x,y,p,u) (z,e1) e2 e3 e4
        end

      (* norm-coerce-trivial *)
      | Syntax.Coerce (alpha, beta, e)
          when Universe.eq alpha beta ->
        whnf ctx (Syntax.mkUniverse ~loc alpha) e

      | Syntax.Coerce (alpha, beta, e) ->
        begin match whnf ctx (Syntax.mkUniverse ~loc alpha) e with
          (* norm-coerce-trans *)
          | (Syntax.Coerce (gamma, delta, e), _) when Universe.eq delta alpha ->
            if Universe.eq gamma beta
            then
              (* norm-coerce-trivial *)
              e
            else
              Syntax.mkCoerce ~loc gamma beta e

          (* norm-coerce-other *)
          | e ->
            Syntax.mkCoerce ~loc alpha beta e
        end

      | (Syntax.Lambda _ | Syntax.Record _ | Syntax.UnitTerm | Syntax.Idpath _ |
         Syntax.Refl _ | Syntax.NameRecordTy _ | Syntax.NameUnit | Syntax.NameProd _ |
         Syntax.NameUniverse _ | Syntax.NamePaths _ | Syntax.NameId _) ->
        e0
    end
  in
    let answer =
      match use_rws, fst e with
      | true, Syntax.Spine _ ->
          rewrite_term ctx e t
      | _, _ -> e
    in
    begin
      if (Syntax.equal answer e0) then
            Print.debug "Term %t was head-normal" (print_term ctx e0)
          else
            Print.debug "@[<hv 4>Rewrote@ %t@;<1 -4> to@ %t@]" (print_term ctx e0) (print_term ctx answer);
      answer
    end

(** [rewrite_term ctx e t] rewrites term [e] of type [t] using rewrite hints
    from [ctx]. After rewriting it re-runs weak head-normalization on the
    resulting term. *)

and rewrite_term ctx e t =
  let count = Common.next()  in
  Print.debug "@[<hv 4>rewrite_term <<%s>> %d:@ %t@]"
      count (List.length (Context.rewrites ctx)) (print_term ctx e) ;

  let match_hint k pt pe1 pe2 =
    (*Print.debug "@[<hv 4>Can we use the hint@ %t@;<1 -4> at@ %t@]"*)
    (*    (print_term ctx e)                                        *)
    (*    (print_pattern ctx k pe1)                                 *)
    (*    (print_pattern_ty ctx k pt) ;                             *)

    let inst = []  in
    let inst =  match_term k inst 0 ctx pe1 e t  in
    let _ = Print.debug "match_hint: instantiation succeeded" in
    let pe2 = Pattern.subst_term inst 0 pe2  in
    match pe2 with
    | Pattern.Term e2 ->
       begin
         (* XXX: This is *not* sufficient to detect uninstantiated variables;
          * only uninstantiated variables used in the right-hand-side.
          * We really need to examine the instantiation. Maybe compare
          * Length.list inst and k? *)

         Print.debug "Success! Hint rewrote to %t" (print_term ctx e2);
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
      let count' = count  in
      begin try
        Print.debug "@[<hv 4><<%s>> Can we use hint that rewrites@ %t@;<1 -4> to@ %t@]"
            count' (print_pattern ctx k pe1) (print_pattern ctx k pe2);
        let e2 = match_hint k pt pe1 pe2 in
        Print.debug "@[<hv 2><<%s>> rewrote@ %t at@ %t@;<1 -2>to@ %t@;<1 -2> using@ %t and@ %t@]"
            count'
            (print_term ctx e) (print_ty ctx t) (print_term ctx e2)
            (print_pattern ctx k pe1) (print_pattern ctx k pe2) ;
          whnf ~use_rws:true ctx t e2
        with
          | Mismatch ->
              Print.debug "<<%s>> nope" count;
                match_hints hs
          (*| Error.Error (_,s1,s2) -> (Print.debug "unexpected Error %s %s" s1 s2; match_hints hs)*)
          | ex -> (Print.debug "unexpected exception %s"
                        (Printexc.to_string ex); match_hints hs)
      end
  in
  let hs = Context.rewrites ctx in
  let answer = match_hints hs  in
  (*let _ = Print.debug "rewrite_term returned %t" (print_term ctx answer) in*)
  answer


(** See if terms [e1] and [e2] of type [t] are equal by an equality hint. *)
and equal_by_equation ctx t e1 e2 =
  (*Print.debug "equal_by_equation? %t@ and %t"*)
  (*   (print_term ctx e1) (print_term ctx e2);*)
  let match_hint k pt pe1 pe2 =
    (*Print.debug "considering hint %t = %t"                *)
    (*  (print_pattern ctx k pe1) (print_pattern ctx k pe2);*)
    let inst = []  in
    (* Match the left-hand-side and incorporate results into the right-hand-side *)
    let inst =  match_term k inst 0 ctx pe1 e1 t  in
    let pt = Pattern.subst_ty inst 0 pt
    and pe1 = Pattern.subst_term inst 0 pe1
    and pe2 = Pattern.subst_term inst 0 pe2 in

    (* Match the right-hand-side *)
    let inst = []  in  (* We substituted away the old inst info *)
    let inst =  match_term k inst 0 ctx pe2 e2 t  in

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
      end
  in
    match_hints (Context.equations ctx)

(* Equality of types *)
and equal_ty' ~use_rws ~use_eqs ctx t u =
  Print.debug "@[<hv 4>equal_ty'@ %t@;<1 -4> and@ %t@]"  (print_ty ctx t) (print_ty ctx u);

  (* chk-tyeq-refl *)
  (Syntax.equal_ty t u)

  ||

  let t = whnf_ty ~use_rws ctx t  in
  let u = whnf_ty ~use_rws ctx u  in
  equal_whnf_ty ~use_eqs ~use_rws ctx t u

(* equality of weak-head-normal types *)
and equal_whnf_ty ~use_eqs ~use_rws ctx ((t', tloc) as t) ((u', uloc) as u) =
  let equal_ty' = equal_ty' ~use_eqs ~use_rws:true
  and equal_term = equal_term ~use_eqs ~use_rws:true
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

    | Syntax.RecordTy lst1, Syntax.RecordTy lst2 ->
      let rec fold ctx lst1 lst2 =
        match lst1, lst2 with
          | [], [] -> true
          | (_::_, []) | ([], _::_) -> false
          | (lbl1,(x,t1)) :: lst1, (lbl2,(_,t2)) :: lst2 ->
            lbl1 = lbl2 &&
            equal_ty' ctx t1 t2 &&
            (let ctx = Context.add_var x t1 ctx in fold ctx lst1 lst2)
      in
        fold ctx lst1 lst2

    | Syntax.El _, _
    | _, Syntax.El _ ->
        begin match Syntax.name_of t, Syntax.name_of u with
          (* chk-tyeq-el *)
          | Some (e1, alpha), Some (e2, beta) ->
            Universe.eq alpha beta &&
            equal_term ctx e1 e2 (Syntax.mkUniverse ~loc:(snd t) alpha)
          | (_, None) | (None, _) -> false
        end

    | (Syntax.Universe _ | Syntax.Unit | Syntax.RecordTy _
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
    (*Print.debug "@[<hv 4>equal_term %b %b:@ %t@;<1 -4> and@ %t@]" *)
    (*      use_eqs use_rws (print_term ctx e1) (print_term ctx e2);*)

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
    let count = Common.next() in
    (*if (not (!tentative)) then*)
      Print.debug "@[<hv 4>equal_ext <<%s>> %b %b:@ %t@;<1 -4> and@ %t@ at %t@]"
            count use_eqs use_rws (print_term ctx e1) (print_term ctx e2)
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
        let z = Syntax.mkVar 0  in         (* ctx, z    |- z : ... *)
        equal_term ~use_eqs ~use_rws ctx'
              (Syntax.mkApp ~loc:loc1 x t' u' e1' z)
              (Syntax.mkApp ~loc:loc2 x t' u' e2' z)
              u

    | Syntax.RecordTy lst ->
      let rec fold ctx e1 e2 lst0 = function
        | [] -> true
        | (lbl,(x,t)) :: lst' ->
          let e1' = Syntax.mkProject ~loc:loc1 e1 lst0 lbl
          and e2' = Syntax.mkProject ~loc:loc2 e2 lst0 lbl
          in
            equal_term ~use_eqs ~use_rws ctx e1' e2' t &&
            (let ctx = Context.add_def x t e1' ctx
             and e1 = Syntax.shift 1 e1
             and e2 = Syntax.shift 1 e2
             and lst0 = List.map (fun (lbl,(x,t)) -> (lbl, (x, Syntax.shift_ty 1 t))) lst0
             in fold ctx e1 e2 lst0 lst')
      in
        fold ctx e1 e2 lst lst

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
  let count = Common.next() in
      Print.debug "@[<hv 4>equal_whnf <<%s>>%s%s:@ %t@;<1 -4> and@ %t@ at %t@]"
            count
            (if use_eqs then " +eqs" else "")
            (if use_rws then " +rws" else "")
            (print_term ctx e1) (print_term ctx e2)
            (print_ty ctx t);
  let equal_ty' = equal_ty' ~use_eqs ~use_rws:true
  and equal_term = equal_term ~use_eqs ~use_rws:true
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


    | Syntax.Spine (f1, fty1, es1), _ ->
        equal_whnf ~use_eqs ~use_rws ctx (Syntax.from_spine ~loc:loc1 f1 fty1 es1) e2 t

    | _, Syntax.Spine (f2, fty2, es2) ->
        equal_whnf ~use_eqs ~use_rws ctx e1 (Syntax.from_spine ~loc:loc2 f2 fty2 es2) t

    (* chk-eq-whnf-app *)
    | Syntax.App((x, t1, u1), ef1, ex1), Syntax.App((_, t2, u2), ef2, ex2) ->
        if tentatively (fun () -> equal_ty' ctx t1 t2
                         && equal_ty' (Context.add_var x t1 ctx) u1 u2
                         && equal_whnf ~use_eqs ~use_rws ctx ef1 ef2
                                       (Syntax.mkProd ~loc:loc1 x t1 u1)) then
           equal_term ctx ex1 ex2 t1
        else
          begin
           ((if (not (!tentative)) then
               Print.warning "@[<hv 2><<%s>>Why are applications@ %t@;<1 -2>and@ %t@;<1 -2>equal?@]"
                    count (print_term ctx e1) (print_term ctx e2));
           false)
          end

    | Syntax.Record lst1, Syntax.Record lst2 ->
      let rec fold ctx lst1 lst2 =
        match lst1, lst2 with
          | [], [] -> true
          | _::_, [] | [], _::_ -> false
          | (lbl1,(x1,t1,e1)) :: lst1, (lbl2,(_,t2,e2)) :: lst2 ->
            lbl1 = lbl2 &&
            (equal_ty' ctx t1 t2) &&
            (equal_term ctx e1 e2 t1) &&
            (let ctx = Context.add_def x1 t1 e1 ctx in fold ctx lst1 lst2)
      in
        fold ctx lst1 lst2

    | Syntax.Project (e1, lst1, lbl1), Syntax.Project (e2, lst2, lbl2) ->
      lbl1 = lbl2 &&
      equal_ty' ctx (Syntax.mkRecordTy lst1) (Syntax.mkRecordTy lst2) &&
      equal_term ctx e1 e2 (Syntax.mkRecordTy lst1)

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
          and zvar = Syntax.mkVar 0                   (* ctx, z |- z *)
          in
            (* ctx, z |- v[z/x,z/y,(idpath z)/p] type *)
            Syntax.strengthen_ty v
              [zvar; zvar; Syntax.mkIdpath s zvar]

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
        && equal_whnf ~use_eqs ~use_rws ctx e2 e2' (Syntax.mkPaths ~loc:loc1 t e3 e4)

    (* chk-eq-whnf-refl *)
    | Syntax.Refl(t, e1), Syntax.Refl(u, e2) ->
        equal_ty' ctx t u && equal_term ctx e1 e2 t

    (* chk-eq-whnf-prod *)
    | Syntax.NameProd (alpha, beta, x, e1, e2),
      Syntax.NameProd (alpha', beta', _, e1', e2') ->
        Universe.eq alpha alpha' && Universe.eq beta beta'
        && equal_term ctx e1 e1' (Syntax.mkUniverse alpha)
        && equal_term (Context.add_var x (Syntax.mkEl alpha e1) ctx)
                 e2 e2' (Syntax.mkUniverse beta)

    (* chk-eq-whnf-universe *)
    | Syntax.NameUniverse alpha, Syntax.NameUniverse beta ->
        Universe.eq alpha beta

    | Syntax.NameRecordTy lst1, Syntax.NameRecordTy lst2 ->
      let rec fold ctx lst1 lst2 =
        match lst1, lst2 with
          | [], [] -> true
          | _::_, [] | [], _::_ -> false
          | (lbl1,(x1,alpha1,e1)) :: lst1, (lbl2,(_,alpha2,e2)) :: lst2 ->
            lbl1 = lbl2 &&
            Universe.eq alpha1 alpha2 &&
            (equal_term ctx e1 e2 (Syntax.mkUniverse alpha1)) &&
            (let ctx = Context.add_var x1 (Syntax.mkEl alpha1 e1) ctx in fold ctx lst1 lst2)
      in
        fold ctx lst1 lst2

    (* chk-eq-whnf-unit *)              (** Subsumed by reflexivity check! *)
    (*| Syntax.NameUnit, Syntax.NameUnit -> true *)

    (* chk-eq-whnf-paths *)
    | Syntax.NamePaths(alpha, e1, e2, e3), Syntax.NamePaths(alpha', e1', e2', e3') ->
        Universe.eq alpha alpha'
        && equal_term ctx e1 e1' (Syntax.mkUniverse alpha)
        && equal_term ctx e2 e2' (Syntax.mkEl alpha e1)
        && equal_term ctx e3 e3' (Syntax.mkEl alpha e1)

    (* chk-eq-whnf-id *)
    | Syntax.NameId(alpha, e1, e2, e3), Syntax.NameId(alpha', e1', e2', e3') ->
        Universe.eq alpha alpha'
        && equal_term ctx e1 e1' (Syntax.mkUniverse alpha)
        && equal_term ctx e2 e2' (Syntax.mkEl alpha e1)
        && equal_term ctx e3 e3' (Syntax.mkEl alpha e1)

    (* chk-eq-whnf-coerce *)
    | Syntax.Coerce(alpha, _beta, e1), Syntax.Coerce(alpha', _beta', e1') ->
        Universe.eq alpha alpha'
        && equal_term ctx e1 e1' (Syntax.mkUniverse alpha)

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
      | Syntax.Lambda _ | Syntax.App _
      | Syntax.Record _ | Syntax.Project _
      | Syntax.Idpath _ | Syntax.J _ | Syntax.Coerce _ | Syntax.NameUnit
      | Syntax.NameRecordTy _ | Syntax.NameProd _ | Syntax.NameUniverse _
      | Syntax.NamePaths _ | Syntax.NameId _), _ ->
         (if (not (!tentative)) then
             Print.warning "@[<hv 2><<%s>>Why are terms@ %t@;<1 -2>and@ %t@;<1 -2>equal?@]"
                  count (print_term ctx e1) (print_term ctx e2));

          false
  end

and as_hint' ~use_rws ctx (_, loc) t =
  let rec collect ctx' u =
    match fst (whnf_ty ~use_rws ctx' u) with
      | Syntax.Prod (x, t1, t2) ->
        let (k, t, e1, e2) = collect (Context.add_var x t1 ctx') t2 in
          (k + 1, t, e1, e2)
      | Syntax.Id (t, e1, e2) -> (0, t, e1, e2)
      | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.RecordTy _ | Syntax.Paths _ ->
        Error.typing ~loc "this expression cannot be used as an equality hint, its type is %t"
          (print_ty ctx t)
  in
  let (k, t, e1, e2) = collect ctx t in
  let pt = Pattern.of_ty k t in
  let pe1 = Pattern.of_term k e1 in
  let pe2 = Pattern.of_term k e2 in
    (k, pt, pe1, pe2)

(* Simple matching of a type pattern against a type. *)
and match_ty k inst l ctx pt ((t',loc) as t) =
  let count = Common.next() in
  let pt = (match inst with [] -> pt | _ -> Pattern.subst_ty inst l pt) in
  Print.debug "@[<hv>match_ty <<%s>>: comparing type %t@;<1 -4> with pattern@ %t@]"
   count (print_ty ctx t) (print_pattern_ty ctx k pt);

  (* We can't try to apply reductions to the original term
   * when pattern-matching, because we're probably trying to
   * figure out whether any reductions apply here!
   *
   * But we can try applying reductions when we recurse
   * on struct subterms.
   *)

  let match_term inst l ctx p e t =
        try
          match_term k inst l ctx p e t
        with Mismatch ->
          begin
           Print.debug "<<%s>> match_ty's match_term trying again with whnf" count;
           let e = whnf ~use_rws:true ctx t e in
           match_term k inst l ctx p e t
          end

  and match_magenta = match_ty k
  and match_ty = match_ty k
  in
  match pt with

    | Pattern.Ty u  ->
      if tentatively (fun () -> equal_ty' ~use_eqs:false ~use_rws:false ctx t u)
      then inst
      else raise Mismatch

    | Pattern.El (alpha, pe) ->
      begin match Syntax.name_of t with
        | None -> raise Mismatch
        | Some (e', beta) ->
          if Universe.eq alpha beta then
            let t = Syntax.mkUniverse ~loc alpha in
              match_term inst l ctx pe e' t
          else
            inst
      end

    | Pattern.RecordTy plst ->
      let rec fold inst l ctx plst tlst =
        match plst, tlst with
          | [], [] -> inst
          | _::_, [] | [], _::_ -> raise Mismatch
          | (lbl,(x,pt)) :: plst, (lbl',(_,t)) :: tlst ->
            if lbl = lbl' then
              let inst = match_ty inst l ctx pt t in
              let inst = fold inst (l+1) (Context.add_var x t ctx) plst tlst
              in
                inst
            else raise Mismatch
      in
        begin match as_recordty' ~use_rws:false ctx t with
          | None -> raise Mismatch
          | Some tlst -> fold inst l ctx plst tlst
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


and count_apps = function
  | Syntax.App (_, e, _), _ -> 1 + count_apps e
  | _ -> 0

and count_pattern_apps = function
  | Pattern.App (_, p, _) ->
      begin
        match count_pattern_apps p with
        | Some n -> Some (n+1)
        | None   -> None
      end
  | Pattern.PVar _ -> None
  | Pattern.Term e -> Some (count_apps e)
  | _ -> Some 0

(* Simple matching of a term pattern against a term. *)
and match_term k inst l ctx p e t =
  let count = Common.next() in
  let p = (match inst with [] -> p | _ -> Pattern.subst_term inst l p)  in
  (*Print.debug "match_term, term %t,@ pat %t"   *)
  (*  (print_term ctx e) (print_pattern ctx k p);*)
  Print.debug "match_term <<%s>>: %t"
    count (print_term ctx e);

  let match_term inst l ctx p e t =
        try match_term k inst l ctx p e t
        with Mismatch ->
          begin
            Print.debug "<<%s>> math_term's match_term trying again with whnf" count;
            let e = whnf ~use_rws:true ctx t e in
            match_term k inst l ctx p e t
          end

  and match_magenta = match_ty k
  and match_ty = match_ty k
  in
  match p with

  | Pattern.Term e' ->
    let t' = type_of ctx e'  in (* XXX! *)
    let inst = tentatively (fun () -> match_ty inst l ctx (Pattern.Ty t') t)  in
    if tentatively (fun () -> equal_term ~use_eqs:false ~use_rws:false ctx e' e t)
    then inst
    else raise Mismatch

  | Pattern.PVar i ->
    begin
      try
        (*Print.debug "PVar: i = %d, depth = %d, l = %d, e = %t"        *)
        (*   i  (List.length (Context.names ctx)) l  (print_term ctx e);*)
        let e' = List.assoc i inst in
        let e'  = Syntax.shift l e'  in
        (*let _ = Print.debug "Repeat on pattern variable %d = %t"*)
        (*              i (print_term ctx e')  in                 *)
        if equal_term ~use_eqs:false ~use_rws:false ctx e' e t
        then inst
        else raise Mismatch
      with
        | Not_found ->
            let e  = Syntax.shift ~exn:Mismatch (- l)  e  in
            (i,e) :: inst
    end

  | Pattern.Lambda (_, pt1, pt2, pe) ->
    begin match fst e with
      | Syntax.Lambda (x, t1, t2, e) ->
        let inst = match_ty inst l ctx pt1 t1 in
        let ctx' = Context.add_var x t1 ctx in
        let inst = match_magenta inst (l+1) ctx' pt2 t2 in
        let inst = match_term inst (l+1) ctx' pe e t2 in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.App ((_, pt1, pt2), pe1, pe2) ->
    begin match fst e with
      | Syntax.App ((x, t1, t2), e1, e2) ->
        (* We know that the term was already whnf'ed, though possibly
         *    without rewrites. Thus, we're unlikely to match unless
         *    we have two "spines" of equal length.
         *)
        begin
          match count_pattern_apps pe1 with
          | Some n -> if n <> (count_apps e1) then
            (* Fail fast if the spine shapes don't match! *)
            raise Mismatch
          | None -> ()  (* Pattern starts with a pattern variable, so
                           a match is possible even with different
                           numbers of applications, e.g,
                            ?P z  matches   f x y z. *)
        end;
        (* We need to match the function part first, since in
           the case of a spine it probably sets metavariables
           (including type families) that occur in the type. *)
        let inst = match_term inst l ctx pe1 e1 (Syntax.mkProd x t1 t2) in
        let inst = match_magenta inst l ctx pt1 t1 in
        let inst = match_magenta inst (l+1) (Context.add_var x t1 ctx) pt2 t2 in
        let inst = match_term inst l ctx pe2 e2 t1 in
          inst
      | Syntax.Spine (f,fty,es) ->
          match_term inst l ctx p (Syntax.from_spine f fty es) t
      | _ -> raise Mismatch
    end

  | Pattern.Spine (pf, _, pes) ->
      begin
        let loc = snd e in
        match fst e with
        | Syntax.Spine (f, fty, es) when ( pf = f && List.length pes = List.length es) ->
            Syntax.fold_left2_spine
              loc
              (fun n t1 t2 inst p e -> match_term inst l ctx p e t1)
              inst f fty pes es

        | _ -> raise Mismatch
      end

  | Pattern.Record plst ->
    let rec fold inst l ctx plst elst =
      match plst, elst with
        | [], [] -> inst
        | _::_, [] | [], _::_ -> raise Mismatch
        | (lbl,(_,pt,pe)) :: plst, (lbl',(x,t,e)) :: tlst ->
          if lbl = lbl' then
            let inst = match_ty inst l ctx pt t in
            let inst = match_term inst l ctx pe e t in
            let inst = fold inst (l+1) (Context.add_var x t ctx) plst tlst
            in
              inst
          else raise Mismatch
    in
      begin match fst e with
        | Syntax.Record elst -> fold inst l ctx plst elst
        | _ -> raise Mismatch
      end

  | Pattern.Project _ ->
    Error.impossible "Equal.match_term: pattern projection not implemented"

  | Pattern.Idpath (pt, pe) ->
    begin match fst e with
      | Syntax.Idpath (t, e) ->
        let inst = match_magenta inst l ctx pt t in
        let inst = match_term inst l ctx pe e t in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.J (pt, (_,_,_,pu), (_,pe1), pe2, pe3, pe4) ->
    begin match fst e with
      | Syntax.J (t, (x,y,p,u), (z,e1), e2, e3, e4) ->
        let inst = match_magenta inst l ctx pt t in
        let ctx_xyp, ctx_z = Context.for_J t x y p z ctx in
        let inst = match_ty inst (l+3) ctx_xyp pu u in
        let inst = match_term inst (l+1) ctx_z pe1 e1 t in
        let inst = match_term inst l ctx pe2 e2 t in
        (* XXX strictly speaking, [e3] and [e4] are magenta, but they are terms *)
        let inst = match_term inst l ctx pe3 e3 t in
        let inst = match_term inst l ctx pe4 e4 t in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.Refl (pt, pe) ->
    begin match fst e with
      | Syntax.Refl (t, e) ->
        let inst = match_magenta inst l ctx pt t in
        let inst = match_term inst l ctx pe e t in
          inst
      | _ -> raise Mismatch
    end

   (** XXX should switch to comparing type names *)

  | Pattern.Coerce (alpha, beta, pe) ->
    begin match fst e with
      | Syntax.Coerce (gamma, delta, e)
          when Universe.eq alpha gamma && Universe.eq beta delta ->
        let inst = match_term inst l ctx pe e (Syntax.mkUniverse alpha) in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.NameRecordTy plst ->
    let rec fold inst l ctx plst elst =
      match plst, elst with
        | [], [] -> inst
        | _::_, [] | [], _::_ -> raise Mismatch
        | (lbl,(_,alpha,pe)) :: plst, (lbl',(x,beta,e)) :: tlst ->
          if lbl = lbl' && alpha = beta then
            let inst = match_term inst l ctx pe e (Syntax.mkUniverse alpha) in
            let inst = fold inst (l+1) (Context.add_var x t ctx) plst tlst
            in
              inst
          else raise Mismatch
    in
      begin match fst e with
        | Syntax.NameRecordTy elst -> fold inst l ctx plst elst
        | _ -> raise Mismatch
      end

  | Pattern.NameProd (alpha, beta, _, pe1, pe2) ->
    begin match fst e with
      | Syntax.NameProd (gamma, delta, x, e1, e2)
          when Universe.eq alpha gamma && Universe.eq beta delta ->
        let inst = match_term inst l ctx pe1 e1 (Syntax.mkUniverse gamma) in
        let inst =
          match_term
            inst
            (l+1)
            (Context.add_var x (Syntax.mkEl gamma e1) ctx)
            pe2
            e2
            (Syntax.mkUniverse delta)
        in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.NamePaths (alpha, pe1, pe2, pe3) ->
    begin match fst e with
      | Syntax.NamePaths (beta, e1, e2, e3)
          when Universe.eq alpha beta ->
        let inst = match_term inst l ctx pe1 e1 (Syntax.mkUniverse beta) in
        let inst = match_term inst l ctx pe2 e1 (Syntax.mkEl beta e1) in
        let inst = match_term inst l ctx pe3 e1 (Syntax.mkEl beta e1) in
          inst
      | _ -> raise Mismatch
    end

  | Pattern.NameId (alpha, pe1, pe2, pe3) ->
    begin match fst e with
      | Syntax.NameId (beta, e1, e2, e3)
          when Universe.eq alpha beta ->
        let inst = match_term inst l ctx pe1 e1 (Syntax.mkUniverse beta) in
        let inst = match_term inst l ctx pe2 e1 (Syntax.mkEl beta e1) in
        let inst = match_term inst l ctx pe3 e1 (Syntax.mkEl beta e1) in
          inst
      | _ -> raise Mismatch
    end

and as_prod' ~use_rws ctx t =
  match fst (whnf_ty ~use_rws ctx t) with

    | Syntax.Prod (x, t1, t2) ->
      Some (x, t1, t2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.RecordTy _
    | Syntax.Paths _ | Syntax.Id _ ->
      None

and as_universe' ~use_rws ctx t =
  match fst (whnf_ty ~use_rws ctx t) with

    | Syntax.Universe alpha ->
      Some alpha

    | Syntax.El _ | Syntax.Unit | Syntax.RecordTy _ | Syntax.Prod _
    | Syntax.Paths _ | Syntax.Id _ ->
        None

and as_recordty' ~use_rws ctx t =
  match fst (whnf_ty ~use_rws ctx t) with

    | Syntax.RecordTy lst ->
      Some lst

    | Syntax.El _ | Syntax.Unit | Syntax.Universe _ | Syntax.Prod _
    | Syntax.Paths _ | Syntax.Id _ ->
      None

and as_paths' ~use_rws ctx t =
  match fst (whnf_ty ~use_rws ctx t) with

    | Syntax.Paths (t, e1, e2) ->
      Some (t, e1, e2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.RecordTy _
    | Syntax.Prod _ | Syntax.Id _ ->
      None

and as_id' ~use_rws ctx t =
  match fst (whnf_ty ~use_rws ctx t) with

    | Syntax.Id (t, e1, e2) ->
      Some (t, e1, e2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.RecordTy _
    | Syntax.Prod _ | Syntax.Paths _ ->
      None

let equal_ty = equal_ty' ~use_eqs:true ~use_rws:true

let as_prod = as_prod' ~use_rws:true
let as_paths = as_paths' ~use_rws:true
let as_id = as_id' ~use_rws:true
let as_universe = as_universe' ~use_rws:true
let as_recordty = as_recordty' ~use_rws:true
let as_hint = as_hint' ~use_rws:true
