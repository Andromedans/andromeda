(** Normalization of expressions. *)

module S = Syntax
module Ctx = Context

(** [norm ctx e] evaluates expression [e] in environment [ctx] to a weak head normal form,
    while [norm ~weak:false ctx e] evaluates to normal form. *)
let rec norm ?(weak=true) =
  let rec loop ctx e =
    match e with

      | S.Var k ->
          begin
            match Ctx.lookup k ctx with
            | Ctx.Definition (_, e') -> loop ctx e'
            | _ -> e
          end

      | S.Lambda (x, t1, e1) ->
        if weak then
          e
        else
          let t1' = normTy ~weak:true ctx t1  in
          let e1' = loop (Ctx.add_parameter x t1' ctx) e1  in
          S.Lambda (x, t1', e1')

      | S.App (e1, e2) ->
          begin
            match loop ctx e1 with
            | S.Lambda(_, _, eBody) ->
                S.beta eBody e2
            | (S.Var _ | S.App _ | S.Proj _) as e1' ->
                let e2' = if weak then e2 else loop ctx e2 in
                S.App(e1', e2')
            | S.Pair _ ->
                Error.typing "Normalization found pair applied to argument"
          end

      | S.Proj (i, e2) ->
          begin
            match loop ctx e2 with
            | S.Pair(e21, e22) ->
                begin
                  match i with
                  (* The input might have been fst(pair(XX, YY)), in which case
                   * weak head normalizing gives us e21 = XX, e22 = YY.
                   * These are either unnormalized (if weak), or fully
                   * normalized (otherwise)
                   *)
                  | 1 -> if weak then loop ctx e21 else e21
                  | 2 -> if weak then loop ctx e22 else e22
                  | i -> Error.typing "Bad projection <> 1 or 2: %d" i
                end
            | e2' -> S.Proj(i, e2')
          end

      | S.Pair (e1, e2) ->
          if weak then
            e
          else
            S.Pair(loop ctx e1, loop ctx e2)
  in
    loop

and normTy ?(weak=true) =
  let rec loop ctx = function
      | S.TVar k as t ->
          begin
            let entry =
              (try Ctx.lookup k ctx with
              | e ->
                  begin
                    print_endline ("normTy: Error in context lookup for variable " ^ (string_of_int k) ^ ". Context is:");
                    Ctx.print ctx;
                    raise e;
                  end)  in
              match entry with
              | Ctx.TyDefinition (_, t') -> loop ctx t'
              | _ -> t
          end

      | S.TPi (x, t1, t2) as t ->
        if weak then
          t
        else
          let t1' = loop ctx t1  in
          let e1' = loop (Ctx.add_parameter x t1' ctx) t2  in
          S.TPi (x, t1', e1')

      | S.TSigma (x, t1, t2) as t ->
        if weak then
          t
        else
          let t1' = loop ctx t1  in
          let e1' = loop (Ctx.add_parameter x t1' ctx) t2  in
          S.TSigma (x, t1', e1')

      | S.TApp (t1, e2) ->
          let t1' = loop ctx t1 in
          let e2' = if weak then e2 else norm ~weak:false ctx e2  in
          S.TApp(t1', e2')
  in
    loop



(** [nf ctx e] computes the normal form of expression [e]. *)
let nf ctx = norm ~weak:false ctx

(** [whnf ctx e] computes the weak head normal form of expression [e]. *)
let whnf ctx = norm ~weak:true ctx

let nfTy ctx = normTy ~weak:false ctx
let whnfTy ctx ty =
  (
   (*Format.printf "WHNFTY in %t@\n" (Print.ty ctx.Ctx.names ty); *)
   let answer = normTy ~weak:true ctx ty in
   (*Format.printf "WHNFTY out %t@\n" (Print.ty ctx.Ctx.names ty);*)
   answer)


