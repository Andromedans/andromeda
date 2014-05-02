(********************)
(* Helper Functions *)
(********************)

let print_ty ctx ty =
  Print.ty (Context.names ctx) ty

let print_term ctx term =
  Print.term (Context.names ctx) term

let print_universe = Print.universe

(************)
(* Equality *)
(************)

(*************************)
(* Weak-Head Normalizing *)
(*************************)

(* Single step for a type *)

let rec whnf_ty ctx ((t',loc) as t) =
  Print.debug "whnf_ty: %t" (print_ty ctx t) ;
  begin match t' with

    (* tynorm-el *)
    | Syntax.El (alpha, e) ->
      begin match fst (whnf ctx (Syntax.Universe alpha, loc) e) with
          
        (* tynorm-pi *)
        | Syntax.NameProd (beta, gamma, x, e1, e2) 
            when Universe.eq alpha (Universe.max beta gamma) ->
          let t1 = whnf_ty ctx (Syntax.El (beta, e1), snd e1) in
          let t2 = whnf_ty (Context.add_var x t1 ctx) (Syntax.El (gamma, e2), snd e2) in
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
          let t1 = whnf_ty ctx (Syntax.El (alpha, e1), snd e1) in
          let e2 = whnf ctx t1 e2 in
          let e3 = whnf ctx t1 e3 in
            Syntax.Paths (t1, e2, e3),
            loc

        (* tynorm-id *)
        | Syntax.NameId (beta, e1, e2, e3) 
            when Universe.eq alpha beta ->
          let t1 = whnf_ty ctx (Syntax.El (alpha, e1), snd e1) in
          let e2 = whnf ctx t1 e2 in
          let e3 = whnf ctx t1 e3 in
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

and whnf ctx t ((e',loc) as e) =
  Print.debug "whnf: %t" (print_term ctx e) ;
  let e =
    begin match e' with
      (* norm-equation *)
      | Syntax.Equation (e1, t1, e2) ->
        whnf (Context.add_equation e1 t1 ctx) t e2

      (* norm-rewrite *)
      | Syntax.Rewrite (e1, t1, e2)  ->
        whnf (Context.add_rewrite e1 t1 ctx) t e2

      (* norm-ascribe *)
      | Syntax.Ascribe(e, _) ->
        whnf ctx t e

      | Syntax.App ((x, u1, u2), e1, e2) ->
        begin
          let e1 = whnf ctx (Syntax.Prod (x, u1, u2), loc) e1 in
            match fst e1 with
              (* norm-app-beta *)
              | Syntax.Lambda (y, t1, t2, e1')
                  when ty ctx u1 t1 && ty (Context.add_var x u1 ctx) u2 t2 ->
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
                  when ty ctx t t' ->
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

      | _ -> e
    end
  in
    match Context.lookup_rewrite t e ctx with
      | None -> e
      | Some e' -> whnf ctx t e'


(* equality of types *)
and ty ctx t u =
  Print.debug "Equal.ty: %t and %t" (print_ty ctx t) (print_ty ctx u) ;
  (* chk-tyeq-refl *)
  (Syntax.equal_ty t u)
  ||
  begin match Syntax.name_of t, Syntax.name_of u with
    (* chk-tyeq-el *)
    | Some (e1, alpha), Some (e2, beta) ->
      Universe.eq alpha beta && term ctx e1 e2 (Syntax.Universe alpha, snd t)
    | (_, None) | (None, _) -> false
  end
  ||
  begin
    let t' = whnf_ty ctx t  in
    let u' = whnf_ty ctx u  in
      equal_whnf_ty ctx t' u'
  end

(* equality of weak-head-normal types *)

and equal_whnf_ty ctx ((t', tloc) as t) ((u', uloc) as u) =
  begin
    Print.debug "equal_whnf_ty: %t == %t@." (print_ty ctx t) (print_ty ctx u);
    match t', u' with

    (* chk-tyeq-path-refl *)
    | _, _ when Syntax.equal_ty t u ->
        true

    (* chk-tyeq-prod *)
    | Syntax.Prod(x, t1, t2), Syntax.Prod(_, u1, u2) ->
        ty ctx t1 u1 &&
        ty (Context.add_var x t1 ctx) t2 u2

    (* chk-tyeq-paths *)
    | Syntax.Paths(t,e1,e2), Syntax.Paths(u,e1',e2') ->
        ty ctx t u &&
        term ctx e1 e1' t &&
        term ctx e2 e2' t

    (* chk-tyeq-id *)
    | Syntax.Id(t,e1,e2), Syntax.Id(u,e1',e2') ->
        ty ctx t u &&
        term ctx e1 e1' t &&
        term ctx e2 e2' t

    | (Syntax.Universe _ | Syntax.El _ | Syntax.Unit
       | Syntax.Prod _ | Syntax.Paths _ | Syntax.Id _), _ ->
           false
  end

(* equality of terms.

   Precondition: t is well-formed
                 term1 : t
                 term2 : t
 *)
and term ctx term1 term2 t =

  Print.debug "equal: %t == %t @@ %t @."
      (print_term ctx term1) (print_term ctx term2) (print_ty ctx t);

  (* chk-eq-refl *)
  if (Syntax.equal term1 term2) then
    true

  (* chk-eq-hint *)
  else if (Context.lookup_equation t term1 term2 ctx) then
    true

  else
    let t' = whnf_ty ctx t in
    equal_ext ctx term1 term2 t'

(* Equality of terms at a weak-head-normal type.

   Precondition: ty is well-formed *and weak-head-normal*
                 e1 : ty
                 e2 : ty
 *)
and equal_ext ctx ((_, loc1) as e1) ((_, loc2) as e2) ((t', _) as t) =
  begin
    Print.debug "equal_ext: %t == %t @@ %t @."
      (print_term ctx e1) (print_term ctx e2) (print_ty ctx t);
    match t' with

    (* chk-eq-ext-prod *)
    | Syntax.Prod(x, t, u) ->
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
        term ctx'
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
    | _ ->
        let e1' = whnf ctx t e1 in
        let e2' = whnf ctx t e2  in
        equal_whnf ctx e1' e2' t
  end

(* equality of two weak-head-normal terms.

   Precondition: term1 : ty
                 term2 : ty
                    for some (unspecified) common type ty.
 *)
and equal_whnf ctx ((term1', loc1) as term1) ((term2', loc2) as term2) t =
  begin
    match term1', term2' with

    (* chk-eq-whnf-reflexivity *)
    | _, _ when Syntax.equal term1 term2 ->
        true

    (* chk-eq-whnf-equation *)
    | _, _ when Context.lookup_equation t term1 term2 ctx ->
        true

    (* chk-eq-whnf-var *)
    | Syntax.Var index1, Syntax.Var index2 -> index1 = index2

    (* chk-eq-whnf-app *)
    | Syntax.App((x, t1, t2), e1, e2), Syntax.App((_, u1, u2), e1', e2') ->
        ty ctx t1 u1
        && ty (Context.add_var x t1 ctx) t2 u2
        && equal_whnf ctx e1 e1' (Syntax.Prod (x, t1, t2), loc1)
        && term ctx e2 e2' t1

    (* chk-eq-whnf-idpath *)
    | Syntax.Idpath(t, e1), Syntax.Idpath(u, e2) ->
        ty ctx t u && term ctx e1 e2 t

    (* chk-eq-whnf-j *)
    | Syntax.J(t1,(x,y,p,u2),(z,e3),e4, e5, e6), Syntax.J(t7, (_,_,_,u8), (_,e9), e10, e11, e12) ->
        let ctx_xy = Context.add_vars
                       [  (x, t1);
                          (y, t1); ] ctx in
        let ctx_xyp = Context.add_vars
                       [  (p, (Syntax.Paths
                                (Syntax.shift_ty 2 t1,  (* Weaken twice for x and y *)
                                (Syntax.Var 0 (* x *), Position.nowhere),
                                (Syntax.Var 1 (* y *), Position.nowhere)),
                                Position.nowhere)) ] ctx_xy  in
        let ctx_z = Context.add_var z t1 ctx  in

        let e3_ty_expected =
                                                         (* ctx,    x, y, p |- u2 type *)
          let u2' = Syntax.weaken_ty 3 u2  in            (* ctx, z, x, y, p |- u2' type *)
                                                         (* ctx    |- t1 type *)
          let t1' = Syntax.weaken_ty 0 t1  in            (* ctx, z |- t1' type *)
          let zvar = (Syntax.Var 0, Position.nowhere) in (* ctx, z |- z *)
          Syntax.strengthen_ty u2'
             [zvar; zvar; (Syntax.Idpath(t1', zvar), Position.nowhere)]
                                              (* ctx, z |- u2'[x,y,p->z,z,idpath z]  type *)  in

        (*
        let j_ty_expected =
          Syntax.strengthen_ty u2 [e5; e6; e4]  in       (* ctx |- u2[x,y,p->e5,e6,e4] *)
        *)

        ty ctx t1 t7
        && ty ctx_xyp u2 u8
        && term ctx_z e3 e9 e3_ty_expected
        && term ctx e5 e11 t1
        && term ctx e6 e12 t1
        && equal_whnf ctx e4 e10 (Syntax.Paths (t1, e5, e6), loc1)

    (* chk-eq-whnf-refl *)
    | Syntax.Refl(t, e1), Syntax.Refl(u, e2) ->
        ty ctx t u && term ctx e1 e2 t

    (* chk-eq-whnf-prod *)
    | Syntax.NameProd(alpha, beta, x, e1, e2), Syntax.NameProd(alpha', beta', _, e1', e2') ->
        Universe.eq alpha alpha' && Universe.eq beta beta'
        && term ctx e1 e1' (Syntax.Universe alpha, Position.nowhere)
        && term (Context.add_var x (Syntax.El(alpha,e1), Position.nowhere) ctx)
                 e2 e2' (Syntax.Universe beta, Position.nowhere)

    (* chk-eq-whnf-universe *)
    | Syntax.NameUniverse alpha, Syntax.NameUniverse beta ->
        Universe.eq alpha beta

    (* chk-eq-whnf-unit *)              (** Subsumed by reflexivity check! *)
    (*| Syntax.NameUnit, Syntax.NameUnit -> true *)

    (* chk-eq-whnf-paths *)
    | Syntax.NamePaths(alpha, e1, e2, e3), Syntax.NamePaths(alpha', e1', e2', e3') ->
        Universe.eq alpha alpha'
        && term ctx e1 e1' (Syntax.Universe alpha, Position.nowhere)
        && term ctx e2 e2' (Syntax.El (alpha, e1), Position.nowhere)
        && term ctx e3 e3' (Syntax.El (alpha, e1), Position.nowhere)

    (* chk-eq-whnf-id *)
    | Syntax.NameId(alpha, e1, e2, e3), Syntax.NameId(alpha', e1', e2', e3') ->
        Universe.eq alpha alpha'
        && term ctx e1 e1' (Syntax.Universe alpha, Position.nowhere)
        && term ctx e2 e2' (Syntax.El (alpha, e1), Position.nowhere)
        && term ctx e3 e3' (Syntax.El (alpha, e1), Position.nowhere)

    (* chk-eq-whnf-coerce *)
    | Syntax.Coerce(alpha, _beta, e1), Syntax.Coerce(alpha', _beta', e1') ->
        Universe.eq alpha alpha'
        && term ctx e1 e1' (Syntax.Universe alpha, Position.nowhere)

    (* chk-eq-whnf-abs *)
    | Syntax.Lambda(x,t1,t2,e1), Syntax.Lambda(_,u1,u2,e2) ->
        ty ctx t1 u1
        && let ctx' = Context.add_var x t1 ctx  in
           ty ctx' t2 u2 && term ctx' e1 e2 t2

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
      | Syntax.NameId _), _ -> false
  end


let as_prod ctx t =
  match fst (whnf_ty ctx t) with

    | Syntax.Prod (x, t1, t2) ->
      Some (x, t1, t2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Paths _ | Syntax.Id _ ->
      None

let as_universe ctx t =
  match fst (whnf_ty ctx t) with

    | Syntax.Universe alpha ->
      Some alpha

    | Syntax.El _ | Syntax.Unit | Syntax.Prod _ | Syntax.Paths _ | Syntax.Id _ ->
        None

let as_paths ctx t =
  match fst (whnf_ty ctx t) with

    | Syntax.Paths (t, e1, e2) ->
      Some (t, e1, e2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Prod _ | Syntax.Id _ ->
      None
