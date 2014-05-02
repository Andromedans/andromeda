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

let rec whnf_ty ctx1 (ty',loc) =
  match ty' with

  (* tynorm-el *)
  | Syntax.El(alpha, ((e', _) as e)) ->
    begin match whnf ctx1 e (Syntax.Universe alpha, loc) with
      | Some (ctx2, e2) ->
          (* Non-backtracking, for now *)
          Some (ctx2, (Syntax.El(alpha, e2), loc))
      | None ->
          begin
            match e' with

            (* tynorm-pi *)
            | Syntax.NameProd(beta, gamma, x, e1, e2) ->
                Some (ctx1,
                      (Syntax.Prod(
                        x,
                        (Syntax.El(beta, e1), loc),
                        (Syntax.El(gamma, e2), loc)), loc))

            (* tynorm-unit *)
            | Syntax.NameUnit ->
                Some (ctx1, (Syntax.Unit, loc))

            (* tynorm-universe *)
            | Syntax.NameUniverse beta ->
                Some (ctx1, (Syntax.Universe beta, loc))

            (* tynorm-coerce *)
            | Syntax.Coerce(_beta,_gamma, e) ->
                Some (ctx1, (Syntax.El(alpha, e), loc))

            (* tynorm-paths *)
            | Syntax.NamePaths(_beta, e1, e2, e3) ->
                Some (ctx1, (Syntax.Paths((Syntax.El(alpha, e1), loc), e2, e3), loc))

            (* tynorm-id *)
            | Syntax.NameId(_beta, e1, e2, e3) ->
                Some (ctx1, (Syntax.Id((Syntax.El(alpha, e1), loc), e2, e3), loc))

            | Syntax.Var _ | Syntax.App _ | Syntax.J _ | Syntax.Lambda _
            | Syntax.UnitTerm | Syntax.Idpath _ | Syntax.Refl _ ->
              None

            (* could have taken a step *)
            | Syntax.Equation _ | Syntax.Rewrite _ | Syntax.Ascribe _ ->
              Error.impossible "normalization of universe names is suprised, please report"
          end
      end

  | (Syntax.Universe _ | Syntax.Unit | Syntax.Prod _ | Syntax.Paths _ | Syntax.Id _) -> None

and whnf ctx ((e',loc) as e) t =
  match Context.lookup_rewrite t e ctx with
  | Some reduct -> Some (ctx, reduct)
  | None ->
      begin
        match e' with
        (* norm-equation *)
        | Syntax.Equation(e1, t, e2) ->
            Some (Context.add_equation e1 t ctx, e2)

        (* norm-rewrite *)
        | Syntax.Rewrite(e1, t, e2)  ->
            Some (Context.add_rewrite e1 t ctx, e2)

        (* norm-ascribe *)
        | Syntax.Ascribe(e, _t) -> Some (ctx, e)

        (* norm-app-beta *)
        | Syntax.App((x,u1,u2),
                     (Syntax.Lambda(_x',t1,t2,e1), _),
                     e2)
            when ty ctx t1 u1
                 && ty (Context.add_var x t1 ctx) t2 u2 ->
            Some (ctx, Syntax.beta e1 e2)

        (* norm-idpath *)
        | Syntax.J(t, (_x,_y,_p,u), (_z,e1),
                   (Syntax.Idpath(t',e2), _), _e3, _e4)
            when ty ctx t t' ->
            Some (ctx, Syntax.beta e1 e2)

        (* norm-coerce-trivial *)
        | Syntax.Coerce(alpha1, alpha2, e)
            when Universe.eq alpha1 alpha2 ->
            Some (ctx, e)

        (* norm-coerce-trans *)
        | Syntax.Coerce(beta1, gamma,
                        (Syntax.Coerce(alpha, beta2, e), _))
            when Universe.eq beta1 beta2 ->
            Some (ctx, e)

        (* norm-app *)
        | Syntax.App((x,t,u), e1, e2) ->
            begin
              match whnf ctx e1 t with
              | Some (ctx, e1') -> Some (ctx, (Syntax.App((x,t,u), e1', e2), loc))
              | None -> None
            end

        (* norm-J *)
        | Syntax.J(t, (x,y,p,u), (z,e1), e2, e3, e4) ->
            begin
              match whnf ctx e2 (Syntax.Paths (t, e3, e4), loc) with
              | Some (ctx, e2') ->
                  Some (ctx, (Syntax.J(t, (x,y,p,u), (z,e1), e2', e3, e4), loc))
              | None -> None
            end

        | _ -> None
      end

(* Repeatedly apply whnf until nothing changes *)
and whnfs ctx1 term1 ty1 =
  match whnf ctx1 term1 ty1 with
  | Some (ctx2, term2) -> whnfs ctx2 term2 ty1
  | None               -> term1

(* Repeatedly apply whnf_ty until nothing changes *)
and whnfs_ty ctx1 ty1 =
  match whnf_ty ctx1 ty1 with
  | Some (ctx2, ty2) -> whnfs_ty ctx2 ty2
  | None             -> ty1

(* equality of types *)

and ty ctx t u =
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
    let t' = whnfs_ty ctx t  in
    let u' = whnfs_ty ctx u  in
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
    let t' = whnfs_ty ctx t in
    equal_ext ctx term1 term2 t'

(* Equality of terms at a weak-head-normal type.

   Precondition: ty is well-formed *and weak-head-normal*
                 e1 : ty
                 e2 : ty
 *)
and equal_ext ctx ((_, loc1) as e1) ((_, loc2) as e2) ((ty', _) as ty) =
  begin
    Print.debug "equal_ext: %t == %t @@ %t @."
      (print_term ctx e1) (print_term ctx e2) (print_ty ctx ty);
    match ty' with

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
    | Syntax.Id (_T, _e3, _e4) ->
        true

    (* chk-eq-ext-whnf *)
    | _ ->
        let e1' = whnfs ctx e1 ty in
        let e2' = whnfs ctx e2 ty in
        equal_whnf ctx e1' e2' ty
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
  match fst (whnfs_ty ctx t) with

    | Syntax.Prod (x, t1, t2) ->
      Some (x, t1, t2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Paths _ | Syntax.Id _ ->
      None

let as_universe ctx t =
  match fst (whnfs_ty ctx t) with

    | Syntax.Universe alpha ->
      Some alpha

    | Syntax.El _ | Syntax.Unit | Syntax.Prod _ | Syntax.Paths _ | Syntax.Id _ ->
        None

let as_paths ctx t =
  match fst (whnfs_ty ctx t) with

    | Syntax.Paths (t, e1, e2) ->
      Some (t, e1, e2)

    | Syntax.Universe _ | Syntax.El _ | Syntax.Unit | Syntax.Prod _ | Syntax.Id _ ->
      None
