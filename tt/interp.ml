module I = InputTT
module SM = InputTT.StringMap

type env =
  {
    ctx : Context.t;
    ttenv : I.exp SM.t;
  }

let empty_env =
  {
    ctx = Context.empty;
    ttenv = SM.empty;
  }

let fresh_name =
  let counter = ref 0 in
  fun () -> (let n = !counter in
             let _ = incr counter in
             "X$" ^ string_of_int n)
(*
let rec eval env ((exp',loc) as exp) =
  match exp' with
  | I.Var v ->
      if SM.mem v env.ttenv then
        SM.find v env.ttenv
      else
        Error.runtime ~loc "Undefined variable %s" v
  | I.Fun (x,c) ->
      I.Closure(x, c, env.ttenv), loc
  | I.Closure _ -> exp
  | I.Handler _ -> exp
  | I.ContExp _ -> exp
  | I.Tuple es -> I.Tuple (List.map (eval env) es), loc
  | I.Const _ -> exp
  | I.Inj(i,e) -> I.Inj(i, eval env e), loc
  | I.DefaultHandler -> exp
  | I.Term _ -> exp
  | I.Type _ -> exp
*)

let rec run env (comp, loc) =
  Print.debug "%s" (I.string_of_computation (comp,loc));
  match comp with
  | I.Val e  ->
      (* eval-val *)
      I.RVal e

  | I.App (e1, e2) ->
      begin
        match fst e1, fst e2 with

        | I.Fun (x,c), _ ->
            (* eval-app *)
            run env (I.subst_computation x e2 c)

        | I.ContExp(gamma,delta,k), _ ->
            (* eval-kapp *)
            if (List.length (Context.names env.ctx) =
                List.length (Context.names gamma) + List.length (Context.names delta)) then
              (* XXX: Should actually check that types match too... *)
              run env (I.kfill e2 k)
            else
              Error.runtime ~loc "Context length mismatch in eval-kapp"

        | _, _ -> Error.runtime ~loc "Bad application"
      end

  | I.Let(x,c1,c2) ->
      begin
        match run env c1 with

        | I.RVal e ->
            (* eval-let-val *)
            run env (I.subst_computation x e c2)

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
                | _, (I.PVar x, c) ->
                    run env (I.subst_computation x e c)

                | I.Tuple es, (I.PTuple xs, c) when List.length es = List.length xs ->
                    (* eval-match-tuple *)
                    let sigma = List.combine xs es  in
                    run env (I.psubst_computation sigma c)

                | I.Inj(i1, e1), (I.PInj (i2, x), c) when i1 = i2 ->
                    (* eval-match-inj *)
                    run env (I.subst_computation x e1 c)

                | I.Const a1, (I.PConst a2, c) when a1 = a2 ->
                    (* eval-match-const *)
                    run env c

                | _, (I.PWild, c) ->
                    run env c

                | _, _ -> loop arms
              end  in
        loop arms

    | I.Op(tag, e) ->
        (* eval-op *)
        I.ROp(tag, Context.empty, e, I.KHole)

    | I.WithHandle(h,c) ->
        begin
          match fst h with
          | I.Handler {I.valH=(x,cv); I.opH}  ->
              begin
                match run env c with
                | I.RVal ev ->
                    (* eval-handle-val *)
                    run env (I.subst_computation x ev cv)
                | I.ROp (opi, delta, e, k1) as r ->
                    begin
                      Print.debug "Handler body produced operation %s" opi;
                      let env' = {env with ctx = Context.append env.ctx delta}  in
                      let k1' = I.ContExp(env.ctx, delta, I.KWithHandle(h, k1)), Position.nowhere  in
                      let handler_result =
                        let rec loop = function
                          | [] -> r
                          | (op, pat, kvar, c)::rest when op = opi ->
                              begin
                                match fst e, pat with
                                | I.Tuple es, I.PTuple xs when List.length es = List.length xs ->
                                    let sigma = (List.combine xs es) @ [ (kvar, k1') ] in
                                    run env' (I.psubst_computation sigma c)

                                | I.Inj(i1,e1), I.PInj(i2,x) ->
                                    run env' (I.psubst_computation [x,e1; kvar,k1'] c)

                                | I.Const a1, I.PConst a2 when a1 = a2 ->
                                    run env' (I.psubst_computation [kvar,k1'] c)

                                | _, I.PVar x ->
                                    run env' (I.psubst_computation [x,e;kvar,k1'] c)

                                | _, I.PWild ->
                                    run env' (I.psubst_computation [kvar,k1'] c)

                                | _, _ -> loop rest
                              end
                          | _ :: rest -> loop rest  in
                        loop opH  in
                      match handler_result with
                      | I.RVal e' ->
                          if eok env e' then
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
        let nvars = List.length (Context.names env.ctx)  in
        if nvars > n then
          I.RVal (I.Term (Syntax.Var n, loc), loc)
        else
          Error.runtime ~loc "Index is %d but context has length %d" n nvars

    | I.MkLam (x1, e2, c3) ->
        begin
          match fst e2 with
          | I.Type t ->
              begin
                let env' = {env with ctx = Context.add_var x1 t env.ctx }  in
                match (run env' c3) with
                | I.RVal v ->
                    (* eval-make-lambda-val *)
                    (* eval-make-lambda-val-tuple *)
                    I.RVal (lambdaize env x1 t v)
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
                | [] -> env.ctx
                | w::ws ->
                    begin
                      match fst w with
                      | I.Term b -> Context.add_equation b (Typing.type_of env.ctx b) (loop ws)
                      | _ -> Error.runtime ~loc "Witness is not a term"
                    end  in
              let ctx' = loop ws in
              if Typing.equiv_ty ctx' t1 t2 then
                run env c   (* XXX questionable whether this should be env' *)
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
                let u = Typing.type_of env.ctx b  in
                let computation =
                  let x1 = fresh_name() in
                  let loc = Position.nowhere in
                  I.Let(x1, (I.Op("equivTy", (I.Tuple [I.Type t, loc; I.Type u, loc], loc)), loc),
                        (I.Check(t, u, (I.Var x1, loc),
                              (I.Val (I.Term (Syntax.Ascribe(b, t), loc), loc), loc)),
                              loc)), loc in
                run env computation

              end
          | I.Term _, _ -> Error.runtime ~loc "Non-type in ascribe"
          | _, _ -> Error.runtime ~loc "Non-term in ascribe"
        end

and eok env exp =
  (* XXX *)
  true

and lambdaize env x t =
  let ctx' = Context.add_var x t env.ctx in
  let rec loop = function
    | I.Term body, loc ->
        I.Term (Syntax.Lambda(x, t, Typing.type_of ctx' body, body), loc), loc
    | I.Tuple es, loc ->
        I.Tuple (List.map loop es), loc
    | (_, loc) -> Error.runtime ~loc "Bad body to MkLam"  in
  loop




