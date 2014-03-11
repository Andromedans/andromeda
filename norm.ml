(** Normalization of terms. *)

module S = BrazilSyntax
module Ctx = BrazilContext.Ctx

(** [whnf ctx e] reduces expression [e] in environment [ctx] to
    weak head normal form *)
let rec whnf ctx e =
  match e with

      | S.Var k ->
          begin
            match Ctx.lookup k ctx with
            | Ctx.Definition (_, e') -> whnf ctx e'
            | _                      -> e
          end


      | S.App (e1, e2) ->
          begin
            match whnf ctx e1 with
            | S.Lambda(_, _, eBody) ->
                whnf ctx (S.beta eBody e2)
            | (S.Var _ | S.App _ | S.Proj _ ) as e1' ->
                S.App(e1', e2)
            | e1' ->
                Error.typing "Normalization found %s applied to argument"
                    (S.string_of_term e1')
          end

      | S.Proj (i, e2) ->
          begin
            match whnf ctx e2 with
            | S.Pair(e21, e22) ->
                begin
                  match i with
                  (* The input might have been fst(pair(XX, YY)), in which case
                   * weak head normalizing gives us e21 = XX, e22 = YY.
                   * These are either unnormalized (if weak), or fully
                   * normalized (otherwise)
                   *)
                  | 1 -> whnf ctx e21
                  | 2 -> whnf ctx e22
                  | i -> Error.typing "Bad projection <> 1 or 2: %d" i
                end
            | e2' -> S.Proj(i, e2')
          end

      | S.Ind_eq(S.Pr, t, (x,y,p,c), (z,w), a, b, q) ->
          begin
            match whnf ctx q with
            | S.Refl (_, a', _) ->
                (* We can only reduce propositional equalities if we
                   are sure they are reflexivity *)
                whnf ctx (S.beta w a')
            | q' -> S.Ind_eq(S.Pr, t, (x,y,p,c), (z,w), a, b, q')
          end

      | S.Ind_eq(S.Ju, _, _, (_,w), a, _, _) ->
          S.beta w a

      | S.Handle (e, es) -> whnf ctx e

        (* Everything else is already in whnf *)
      | S.Lambda _
      | S.Pair _
      | S.Refl _
      | S.Pi _
      | S.Sigma _
      | S.Eq _
      | S.U _
      | S.Const _
      | S.Base _ -> e




(** [nf ctx e] reduces expression [e] in environment [ctx] to a normal form *)
let rec nf ctx e =

    match whnf ctx e with

      | S.Var _ as e' -> e'

      | S.Lambda (x, t1, e1) ->
          let t1' = nf ctx t1  in
          let e1' = nf (Ctx.add_parameter x t1' ctx) e1  in
          S.Lambda (x, t1', e1')

      | S.App (e1, e2) ->
          begin
            (* If e1 e2 is in whnf, then e1 cannot reduce to a lambda *)
            let e1' = nf ctx e1  in
            let e2' = nf ctx e2  in
            S.App(e1', e2')
          end

      | S.Proj (i, e2) ->
          let e2' = nf ctx e2  in
          S.Proj(i, e2')

      | S.Pair (e1, e2) ->
          let e1' = nf ctx e1  in
          let e2' = nf ctx e2  in
          S.Pair(e1', e2')

      | S.Refl (z, e1, t1) ->
          let e1' = nf ctx e1  in
          let t1' = nf ctx t1  in
          S.Refl(z, e1', t1')

      | S.Pi (x, t1, t2) ->
          let t1' = nf ctx t1  in
          let e1' = nf (Ctx.add_parameter x t1' ctx) t2  in
          S.Pi (x, t1', e1')

      | S.Sigma (x, t1, t2) ->
          let t1' = nf ctx t1  in
          let e1' = nf (Ctx.add_parameter x t1' ctx) t2  in
          S.Sigma (x, t1', e1')

      | S.Eq(z, e1, e2, t1) ->
            let e1' = nf ctx e1  in
            let e2' = nf ctx e2  in
            let t1' = nf ctx t1  in
            S.Eq(z, e1', e2', t1')

      | S.Ind_eq(S.Pr, t, (x,y,p,c), (z,w), a, b, q) ->
          (* whnf would have noticed if q reduces to refl *)
          let ctx_c = Ctx.add_parameter p (S.shift 2 (S.Eq(S.Pr, a, b, t)))
                           (Ctx.add_parameter y (S.shift 1 t)
                              (Ctx.add_parameter x t ctx))  in
          let ctx_w = Ctx.add_parameter z t ctx in
          let t' = nf ctx t  in
          let c' = nf ctx_c c  in
          let w' = nf ctx_w w  in
          let a' = nf ctx a  in
          let b' = nf ctx b  in
          let q' = nf ctx q  in
          S.Ind_eq(S.Pr, t', (x,y,p,c'), (z,w'), a', b', q')

      | S.Ind_eq (S.Ju, _, _, _, _, _, _) ->
          Error.typing "Found a judgmental Ind_eq after whnf"

      | S.Handle (_,_) ->
          Error.typing "Found a top-level handle after whnf"

      | (S.U _ | S.Base _ | S.Const _) as term -> term


