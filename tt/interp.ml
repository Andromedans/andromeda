module I = InputTT

let fresh_name =
  let counter = ref 0 in
  fun () -> (let n = !counter in
             let _ = incr counter in
             "X$" ^ string_of_int n)

let rec run ctx (comp, loc) =
  match comp with
  | I.Val e  ->
      (* eval-val *)
      I.RVal e

  | I.App (e1, e2) ->
      begin
        match fst e1, fst e2 with

        | I.Fun (x,c), _ ->
            (* eval-app *)
            run ctx (I.subst_computation x e2 c)

        | I.ContExp(gamma,delta,k), _ ->
            (* eval-kapp *)
            if (List.length (Context.names ctx) =
                List.length (Context.names gamma) + List.length (Context.names delta)) then
              (* XXX: Should actually check that types match too... *)
              run ctx (I.kfill e2 k)
            else
              Error.runtime ~loc "Context length mismatch in eval-kapp"

        | _, _ -> Error.runtime ~loc "Bad application"
      end

  | I.Let(x,c1,c2) ->
      begin
        match run ctx c1 with

        | I.RVal e ->
            (* eval-let-val *)
            run ctx (I.subst_computation x e c2)

        | I.ROp(op, delta, e, k) ->
            (* eval-let-op *)
            I.ROp(op, delta, e, I.KLet(x,k,c2))
      end

    | I.Match(e, arms) ->
        let rec loop = function
          | [] -> Error.runtime ~loc "No matching pattern found"
          |  arm::arms ->
              begin
                match fst e, arm with
                | I.Tuple es, (I.PTuple xs, c) when List.length es = List.length xs ->
                    (* eval-match-tuple *)
                    let sigma = List.combine xs es  in
                    run ctx (I.psubst_computation sigma c)

                | I.Inj(i1, e1), (I.PInj (i2, x), c) when i1 = i2 ->
                    (* eval-match-inj *)
                    run ctx (I.subst_computation x e1 c)

                | I.Const a1, (I.PConst a2, c) when a1 = a2 ->
                    (* eval-match-const *)
                    run ctx c

                | _, _ -> loop arms
              end  in
        loop arms

    | I.Op(tag, e) ->
        (* eval-op *)
        I.ROp(tag, Context.empty, e, I.KHole)

    | I.WithHandle(e,c) ->
        begin
          match fst e with
          | I.Handler {I.valH=(x,cv); I.opH}  ->
              begin
                match run ctx c with
                | I.RVal ev ->
                    (* eval-handle-val *)
                    run ctx (I.subst_computation x ev cv)
                | I.ROp (opi, delta, e, k1) as r ->
                    begin
                      let ctx' = Context.append ctx delta  in
                      let k1' = I.ContExp(ctx, delta, I.KWithHandle(e, k1)), Position.nowhere  in
                      let handler_result =
                        let rec loop = function
                          | [] -> r
                          | (op, pat, kvar, c)::rest ->
                              begin
                                match fst e, pat with
                                | I.Tuple es, I.PTuple xs when List.length es = List.length xs ->
                                    let sigma = (List.combine xs es) @ [ (kvar, k1') ] in
                                    run ctx' (I.psubst_computation sigma c)

                                | I.Inj(i1,e1), I.PInj(i2,x) ->
                                    run ctx' (I.psubst_computation [x,e1; kvar,k1'] c)

                                | I.Const a1, I.PConst a2 when a1 = a2 ->
                                    run ctx' (I.psubst_computation [kvar,k1'] c)

                                | _, _ -> loop rest
                              end  in
                        loop opH  in
                      match handler_result with
                      | I.RVal e' ->
                          if eok ctx e' then
                            I.RVal e'
                          else
                            Error.runtime ~loc "Handler returned value with too many variables"
                      | I.ROp(opj, delta', e', k2) ->
                          I.ROp(opj, Context.append delta delta', e', k2)
                    end
              end
         | _ ->
              Error.runtime ~loc "Non-handler expression given to with/handle"
        end

    | I.MkVar n ->
        (* eval-make-var *)
        let nvars = List.length (Context.names ctx)  in
        if nvars > n then
          I.RVal (I.Term (Syntax.Var n, loc), loc)
        else
          Error.runtime ~loc "Index is %d but context has length %d" n nvars

    | I.MkLam (x1, e2, c3) ->
        begin
          match fst e2 with
          | I.Type t ->
              begin
                let ctx' = Context.add_var x1 t ctx  in
                match (run ctx' c3) with
                | I.RVal v ->
                    (* eval-make-lambda-val *)
                    (* eval-make-lambda-val-tuple *)
                    I.RVal (lambdaize ctx x1 t v)
                | I.ROp (op, delta, e, k) ->
                    (* eval-make-lambda-op *)
                    let delta0 = Context.add_var x1 t Context.empty in
                    I.ROp (op, Context.append delta0 delta, e, I.KMkLam(x1, t, k))
              end
          | _ -> Error.runtime ~loc "Annotation in MkLam is not a type"
        end

    | I.Check(t1, t2, e, c) ->
        begin
          (* eval-assert-type *)
          match fst e with
          | I.Tuple ws ->
              let rec loop = function
                | [] -> ctx
                | w::ws ->
                    begin
                      match fst w with
                      | I.Term b -> Context.add_equation b (Typing.type_of ctx b) (loop ws)
                      | _ -> Error.runtime ~loc "Witness is not a term"
                    end  in
              let ctx' = loop ws in
              if Typing.equiv_ty ctx' t1 t2 then
                run ctx c   (* XXX questionable whether this should be ctx' *)
              else
                Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
          | _ -> Error.runtime ~loc "Evidence in Check was not a tuple"
        end

    | I.Prim(op, es) ->
        begin
          (* eval-prim *)
          let answer =
            match op, es with
            | I.Not, [I.Const(I.Bool b), _] -> I.Const(I.Bool (not b))
            | I.And, [I.Const(I.Bool b1), _; I.Const(I.Bool b2), _] ->
                  I.Const(I.Bool (b1 && b2))
            | I.Plus, [I.Const(I.Int n1), _; I.Const(I.Int n2), _] ->
                  I.Const(I.Int (n1 + n2))
            | I.Append, [I.Tuple es1, _; I.Tuple es2, _] ->
                  I.Tuple (es1 @ es2)
            | _, _ -> Error.runtime ~loc "Bad arguments to primitive"  in
          I.RVal (answer, Position.nowhere)
        end

    | I.Ascribe(e1, e2) ->
        begin
          match fst e1, fst e2 with
          | I.Term b, I.Type t ->
              begin
                let u = Typing.type_of ctx b  in
                let computation =
                  let x1 = fresh_name() in
                  let loc = Position.nowhere in
                  I.Let(x1, (I.Op("equivTy", (I.Tuple [I.Type t, loc; I.Type u, loc], loc)), loc),
                        (I.Check(t, u, (I.Var x1, loc),
                              (I.Val (I.Term (Syntax.Ascribe(b, t), loc), loc), loc)),
                              loc)), loc in
                run ctx computation

              end
          | I.Term _, _ -> Error.runtime ~loc "Non-type in ascribe"
          | _, _ -> Error.runtime ~loc "Non-term in ascribe"
        end

and eok ctx exp =
  (* XXX *)
  true

and lambdaize ctx x t =
  let ctx' = Context.add_var x t ctx in
  let rec loop = function
    | I.Term body, loc ->
        I.Term (Syntax.Lambda(x, t, Typing.type_of ctx' body, body), loc), loc
    | I.Tuple es, loc ->
        I.Tuple (List.map loop es), loc
    | (_, loc) -> Error.runtime ~loc "Bad body to MkLam"  in
  loop




