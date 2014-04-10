
let rec whnf_ty ctx1 (ty',loc) =
  match ty' with

  | Syntax.El(alpha, ((e', _) as e)) ->
      begin
        (* tynorm-el *)
        match whnf ctx1 e with
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

            (* tynorm-coerce *)
            | Syntax.Coerce(_beta,_gamma, e) ->
                Some (ctx1, (Syntax.El(alpha, e), loc))

            (* tynorm-paths *)
            | Syntax.NamePaths(_beta, e1, e2, e3) ->
                Some (ctx1, (Syntax.Paths((Syntax.El(alpha, e1), loc), e2, e3), loc))

            (* tynorm-id *)
            | Syntax.NameId(_beta, e1, e2, e3) ->
                Some (ctx1, (Syntax.Id((Syntax.El(alpha, e1), loc), e2, e3), loc))

            | _ -> None
          end
      end

  | (Syntax.Universe _ | Syntax.Unit | Syntax.Prod _ | Syntax.Paths _ | Syntax.Id _) -> None

and whnf ctx1 ((term',loc) as term) =
  match Context.lookup_rewrite term ctx1 with
  | Some reduct -> Some (ctx1, reduct)
  | None ->
      begin
        match term' with
        (* norm-equation *)
        | Syntax.Equation(_e1, e2) ->
            Some (ctx1, e2) (* XXX: add hint to this context! *)

        (* norm-rewrite *)
        | Syntax.Rewrite(_e1, e2)  ->
            Some (ctx1, e2)  (* XXX: add hint to this context! *)

        (* norm-ascribe *)
        | Syntax.Ascribe(e, _t) -> Some (ctx1, e)

        (* norm-app-beta *)
        | Syntax.App((x,u1,u2),
                     (Syntax.Lambda(_x',t1,t2,e1), _),
                     e2)
            when equiv_ty ctx1 t1 u1
                 && equiv_ty (Context.add_var x t1 ctx1) t2 u2 ->
            Some (ctx1, Syntax.subst 0 e2 e1)

        (* norm-idpath *)
        | Syntax.J(t, (_x,_y,_p,u), (_z,e1),
                   (Syntax.Idpath(t',e2), _), _e3, _e4)
            when equiv_ty ctx1 t t' ->
            Some (ctx1, Syntax.subst 0 e2 e1)

        (* norm-coerce-trivial *)
        | Syntax.Coerce(alpha1, alpha2, e)
            when alpha1 = alpha2 ->
            Some (ctx1, e)

        (* norm-coerce-trans *)
        | Syntax.Coerce(beta1, gamma,
                        (Syntax.Coerce(alpha, beta2, e), _))
            when beta1 = beta2 ->
            Some (ctx1, e)

        (* norm-app *)
        | Syntax.App((x,t,u), e1, e2) ->
            begin
              match whnf ctx1 e1 with
              | Some (ctx2, e1') -> Some (ctx2, (Syntax.App((x,t,u), e1', e2), loc))
              | None -> None
            end

        (* norm-J *)
        | Syntax.J(t, (x,y,p,u), (z,e1), e2, e3, e4) ->
            begin
              match whnf ctx1 e2 with
              | Some (ctx2, e2') ->
                  Some (ctx2, (Syntax.J(t, (x,y,p,u), (z,e1), e2', e3, e4), loc))
              | None -> None
            end

        | _ -> None
      end

and equiv_ty ctx ty1 ty2 = failwith "not implemented"

(* Repeatedly apply whnf until nothing changes *)
let rec whnfs ctx1 term1 =
  match whnf ctx1 term1 with
  | Some (ctx2, term2) -> whnfs ctx2 term2
  | None               -> term1

(* Repeatedly apply whnf_ty until nothing changes *)
let rec whnfs_ty ctx1 ty1 =
  match whnf_ty ctx1 ty1 with
  | Some (ctx2, ty2) -> whnfs_ty ctx2 ty2
  | None             -> ty1

let rec syn_term ctx e = failwith "not implemented"

and chk_term ctx e t = failwith "not implemented"



