
(* I strongly suspect that we will want to return a reduct
 * and a context with added hints. But that's not what the
 * LaTeX rules say right now...
 *)
let rec whnf ctx ((term',loc) as term) =
  match Context.lookup_rewrite term ctx with
  | Some reduct -> Some reduct
  | None ->
      begin
        match term' with
        (* norm-equation *)
        | Syntax.Equation(_e1, e2) -> Some e2

        (* norm-rewrite *)
        | Syntax.Rewrite(_e1, e2)  -> Some e2

        (* norm-ascribe *)
        | Syntax.Ascribe(e, _t) -> Some e

        (* norm-app-beta *)
        | Syntax.App((x,u1,u2),
                     (Syntax.Lambda(_x',t1,t2,e1), _),
                     e2)
            when equiv_ty ctx t1 u1
                 && equiv_ty (Context.add_var x t1 ctx) t2 u2 ->
            Some (Syntax.subst 0 e2 e1)

        (* norm-idpath *)
        | Syntax.J(t, (_x,_y,_p,u), (_z,e1),
                   (Syntax.Idpath(t',e2), _), _e3, _e4)
            when equiv_ty ctx t t' ->
            Some (Syntax.subst 0 e2 e1)

        (* norm-coerce-trivial *)
        | Syntax.Coerce(alpha1, alpha2, e)
            when alpha1 = alpha2 ->
            Some e

        (* norm-coerce-trans *)
        | Syntax.Coerce(beta1, gamma,
                        (Syntax.Coerce(alpha, beta2, e), _))
            when beta1 = beta2 ->
            Some e

        (* norm-app *)
        | Syntax.App((x,t,u), e1, e2) ->
            begin
              match whnf ctx e1 with
              | Some e1' -> Some (Syntax.App((x,t,u), e1', e2), loc)
              | None -> None
            end

        (* norm-J *)
        | Syntax.J(t, (x,y,p,u), (z,e1), e2, e3, e4) ->
            begin
              match whnf ctx e2 with
              | Some e2' ->
                  Some (Syntax.J(t, (x,y,p,u), (z,e1), e2', e3, e4), loc)
              | None -> None
            end

        | _ -> None
      end

and equiv_ty ctx ty1 ty2 = failwith "not implemented"

let rec syn_term ctx e = failwith "not implemented"

and chk_term ctx e t = failwith "not implemented"



