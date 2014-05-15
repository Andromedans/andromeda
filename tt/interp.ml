module I = InputTT
module SM = InputTT.StringMap

let depth ctx =
  List.length (Context.names ctx)

let insert_ttvar x v ctx env =
  let current_depth = depth ctx in
  SM.add x (v,current_depth) env


(********************)
(* Helper Functions *)
(********************)

(* Printing *Syntax* types and terms *)

let print_ty ctx ty =
  Print.ty (Context.names ctx) ty

let print_term ctx term =
  Print.term (Context.names ctx) term

let print_universe = Print.universe

let string_of_env ctx (env : I.environment) =
        let current_depth = depth ctx in
  "[" ^ String.concat "," (List.map (fun (k,(v,i)) -> k^"="^(I.string_of_value ctx (I.shiftv 0 (current_depth - i) v))) (SM.bindings env)) ^ "]"

(* Gensym *)

let fresh_name =
  let counter = ref 0 in
  fun () -> (let n = !counter in
             let _ = incr counter in
             "X$" ^ string_of_int n)




(** [abstract ctx x t v] wraps every *Brazil* term in v with a (Brazil) lambda.
    For simplicity, we assume that x:t is already the (last) binding in ctx
    It expects that v is either a term or a tuple of terms (or a tuple of these, etc.)
 *)
let abstract ctx x t =
  let rec loop = function
    | I.VTerm body, loc -> I.mkVTerm ~loc (Syntax.Lambda(x, t, Typing.type_of ctx body, body), loc)
    | I.VTuple es, loc  -> I.mkVTuple ~loc (List.map loop es)
    | I.VInj (i, e), loc -> I.mkVInj ~loc i (loop e)
    | (_, loc) -> Error.runtime ~loc "Bad body to MkLam"  in
  loop


let witness_of_value ctx0 = function
  | I.VTerm b, _  -> b
  | (_, loc) as w -> Error.runtime ~loc "Witness %s is not a term" (I.string_of_value ctx0 w)

let extend_context_with_witness ctx v =
  let w = witness_of_value ctx v  in
  let t = Typing.type_of ctx w  in
  let hint = Equal.as_hint ctx w t  in
  Context.add_equation hint ctx

let extend_context_with_witnesses =
  List.fold_left extend_context_with_witness


let wrap_syntax_with_witness ctx b v =
  let w = witness_of_value ctx v in
  Syntax.Equation(w, Typing.type_of ctx w, b), Position.nowhere

let wrap_syntax_with_witnesses ctx =
  List.fold_left (wrap_syntax_with_witness ctx)


let retSomeTuple ws = I.RVal (I.mkVInj 1 (I.mkVTuple ws))
let retNone         = I.RVal (I.mkVInj 0 (I.mkVConst I.Unit))


(*******************************************)
(* Run-time parsing of literal Brazil code *)
(*******************************************)

let parse_literal parse_fn loc text =
     let lexbuf = Lexing.from_string text in
     try
        parse_fn Lexer.token lexbuf
     with
      | Parser.Error ->
          let inner_loc = Position.of_lex lexbuf  in
          Error.syntax ~loc "Brazil code at %s" (Position.to_string inner_loc)
      | Failure "lexing: empty token" ->
          let inner_loc = Position.of_lex lexbuf  in
          Error.syntax ~loc "unrecognized symbol in Brazil literal at %s." (Position.to_string inner_loc)

(********************)
(* Pattern-Matching *)
(********************)

exception NoPatternMatch

(* [insert_matched env (v,pat)] either inserts the TT values from [v] where there
   are corresponding variables in [pat], or raises the [NoPatternMatch]
   exception if [pat] and [v] don't have the same form.
 *)
let rec insert_matched ctx env (v,pat) =
  match fst v, pat with
  | _,             I.PWild    -> env
  | _,             I.PVar x   -> insert_ttvar x v ctx env
  | I.VConst a1,   I.PConst a2    when a1 = a2  ->  env
  | I.VInj(i1,v1), I.PInj (i2,p2) when i1 = i2  ->  insert_matched ctx env (v1, p2)
  | I.VTuple vs,   I.PTuple ps    when List.length vs = List.length ps ->
      List.fold_left (insert_matched ctx) env (List.combine vs ps)
  | _, I.PWhen(p,e) ->
      begin
        let env' = insert_matched ctx env (v,p)  in
        match eval ctx env' e with
        | I.VConst(I.Bool true), _ -> env'
        | _ -> raise NoPatternMatch
      end

  | I.VType (Syntax.Id(_,b1,b2),loc), I.PJuEqual(pat1, pat2) ->
      List.fold_left (insert_matched ctx) env [I.mkVTerm ~loc b1,pat1; I.mkVTerm ~loc b2,pat2]
  | I.VTerm (Syntax.NameProd(alpha,beta,x,b1,b2),loc), I.PProd(pat1,pat2) ->
      insert_matched ctx (insert_matched ctx env (I.mkVTerm ~loc b1, pat1))
             (I.mkVTerm ~loc
             (Syntax.Lambda(x,(Syntax.El(alpha,b1),loc),(Syntax.Universe beta, loc), b2),loc), pat2)
  | I.VTerm (Syntax.NameProd(alpha,beta,x,b1,b2),loc), I.PProdFull(pat1,pat2,pat3,pat4) ->
      let env = insert_matched ctx env (I.mkVTerm ~loc b1, pat1)  in
      let env = insert_matched ctx env
           (I.mkVTerm ~loc (Syntax.Lambda(x,(Syntax.El(alpha,b1),loc),(Syntax.Universe beta, loc), b2),loc), pat3)  in
      let env = insert_matched ctx env (I.mkVType ~loc (Syntax.Universe alpha, loc), pat2)  in
      let env = insert_matched ctx env (I.mkVType ~loc (Syntax.Universe beta, loc), pat4)  in
      env

  | _, (I.PConst _ | I.PInj _ | I.PTuple _
        | I.PJuEqual _ | I.PProd _ | I.PProdFull _ ) -> raise NoPatternMatch


(**************************)
(* Evaluating Expressions *)
(**************************)

(* [eval env e] deterministically reduces TT expression [e] to a
   value. This largely involves looking up
   variables in the environment, and building closures.
 *)
and eval ctx env (exp', loc) =
  match exp' with
  | I.Value v   -> v
  | I.Var x ->
      if SM.mem x env then
        let (value, insert_depth) = SM.find x env  in
        let current_depth = depth ctx in
        let delta = current_depth - insert_depth in
        assert (delta >= 0);
        I.shiftv 0 delta value
      else
        Error.runtime ~loc "Undefined variable %s" x
  | I.Const a   -> I.VConst a, loc
  | I.Term b    -> I.VTerm b, loc
  | I.Type t    -> I.VType t, loc
  | I.Fun (f, x,c) -> I.VFun((fun env ctx self v ->
                                 let env' = insert_ttvar f self ctx env  in
                                 let env' = insert_ttvar x v ctx env'  in
                                 run ctx env' c), env ), loc
  | I.Handler h -> I.VHandler (eval_handler loc h, env), loc
  | I.Tuple es  -> I.VTuple (List.map (eval ctx env) es), loc
  | I.Inj(i,e)  -> I.VInj(i, eval ctx env e), loc
  | I.Prim(op, es) -> eval_prim ctx env loc op (List.map (eval ctx env) es)
  | I.BrazilTermCode text -> eval_brazilterm ctx loc text
  | I.BrazilTypeCode text -> eval_braziltype ctx loc text



and eval_brazilterm ctx loc text =
        begin
          let term = parse_literal Parser.topterm loc text  in
          let term = Debruijn.term (Context.names ctx) term in
          let term, _ty = Typing.syn_term ctx term  in
          I.mkVTerm ~loc term
        end

and eval_braziltype ctx loc text =
        begin
          let term = parse_literal Parser.topty loc text  in
          let ty = Debruijn.ty (Context.names ctx) term in
          let ty = Typing.is_type ctx ty  in
          I.mkVType ~loc ty
        end



and eval_prim ctx env loc op vs =
    match op, vs with
    | I.Not, [I.VConst(I.Bool b), _]  -> I.mkVConst(I.Bool (not b))
    | I.And, [I.VConst(I.Bool b1), _;
              I.VConst(I.Bool b2), _] -> I.mkVConst(I.Bool (b1 && b2))
    | I.Plus, [I.VConst(I.Int n1), _;
               I.VConst(I.Int n2), _] -> I.mkVConst(I.Int (n1 + n2))
    | I.Minus, [I.VConst(I.Int n1), _;
               I.VConst(I.Int n2), _] -> I.mkVConst(I.Int (n1 - n2))
    | I.Times, [I.VConst(I.Int n1), _;
               I.VConst(I.Int n2), _] -> I.mkVConst(I.Int (n1 * n2))
    | I.Append, [I.VTuple es1, _;
                 I.VTuple es2, _]     -> I.mkVTuple (es1 @ es2)
    | I.Append, [I.VConst(I.String s1), _;
                 I.VConst(I.String s2), _]     -> I.mkVConst (I.String (s1 ^ s2))
    | I.Eq,  [a1; a2] -> I.mkVConst( I.Bool (     I.eqvalue a1 a2))
    | I.Neq, [a1; a2] -> I.mkVConst( I.Bool (not (I.eqvalue a1 a2)))
    | I.Whnf, [I.VTerm b, _] ->
        let t = Typing.type_of ctx b  in
        I.mkVTerm (Equal.whnf ~use_rws:true ctx t b)
    | I.Whnf, [I.VType t, _] ->
        I.mkVType (Equal.whnf_ty ~use_rws:true ctx t)
    | I.GetCtx, [] ->
        (Context.print ctx;
        I.mkVConst ~loc (I.Int (List.length (Context.names ctx))))




    | _, _ -> Error.runtime ~loc "Bad arguments to primitive"


and eval_handler loc {I.valH; I.opH; I.finH} =
  let rec hfun env ctx = function
    | I.RVal v ->
        begin
          Print.debug "Handler %s produced value %s@." (Position.to_string loc) (I.string_of_value ctx v);
          match valH with
          | Some (xv,cv) ->
              (* eval-handle-val *)
              run ctx (insert_ttvar xv v ctx env) cv
          | None ->
              I.RVal v
        end

    | I.ROp (opi, delta, v, (k,eta)) ->
        begin
          Print.debug "Handler produced operation %s@." opi;

          let k' env ctx u = hfun env ctx (k eta ctx u)  in
          let rec loop = function
            | [] ->
                (Print.debug "No matching case found for body %s@." (Position.to_string loc);
                I.ROp(opi, delta, v, (k',env)))
            | (op, pat, kvar, c)::rest when op = opi ->
                begin
                  try
                    Print.debug "Found matching case %s. Creating VCont with env =
                      %s" op (string_of_env ctx env);
                    let kval = I.mkVCont ctx delta (k',env) in
                    let ctx_h = Context.append ctx delta  in
                    let env_h = insert_matched ctx_h env (v,pat) in
                    let env_h = insert_ttvar kvar kval ctx_h env_h  in
                    match run ctx_h env_h c with
                      | I.RVal v' ->
                          let unshift_amount = - (List.length (Context.names delta)) in
                          if vok env v' then
                            I.RVal (I.shiftv 0 unshift_amount v')
                          else
                            Error.runtime ~loc "Handler returned value with too many variables"
                      | I.ROp(opj, delta', e', k') ->
                          I.ROp(opj, Context.append delta delta', e', k')
                  with
                    NoPatternMatch -> loop rest
                end
            | _ :: rest -> loop rest in
          loop opH
        end
    in
       fun env ctx r ->
         begin
           match finH with
           | None -> (hfun env ctx r)
           | Some (xf,cf) ->
               sequence (fun v -> run ctx (insert_ttvar xf v ctx env) cf) (hfun env ctx r)
         end


and sequence ?withdelta k = function
  | I.RVal v -> k v
  | I.ROp(tag,delta,v,(k',eta)) ->
      begin
        let k'' env ctx u = sequence k (k' env ctx u)  in
        match withdelta with
        | None -> I.ROp(tag,delta,v,(k'',eta))
        | Some (x,t) ->
            let ctx0 = Context.add_var x t Context.empty in
            I.ROp(tag, Context.append ctx0 delta, v, (k'',eta))
      end



(*************************)
(* Running a Computation *)
(*************************)


and run ctx env  (comp, loc) =
  Print.debug "run: %s\n%s" (I.string_of_computation ctx (comp,loc))
  (string_of_env ctx env);

  match comp with

  | I.Return e  ->
      I.RVal (eval ctx env e)

  | I.App (e1, e2) ->
      begin
        Print.debug "App. env = %s@." (string_of_env ctx env);
        let v1 = eval ctx env e1  in
        let v2 = eval ctx env e2  in
        Print.debug "v1 = %s, v2 = %s@." (I.string_of_value ctx v1)
        (I.string_of_value  ctx v2);
        match fst v1, fst v2 with

        | I.VFun (f,eta), _ ->
            (* Extend _closure_ environment with argument
               and run the function body
             *)
            f eta ctx v1 v2

        | I.VCont(gamma,delta,(k,eta)), _ ->
            (* eval-kapp *)
            Print.debug "Applying vcont. env = %s@." (string_of_env ctx env);
            if (List.length (Context.names ctx) =
                List.length (Context.names gamma) + List.length (Context.names delta)) then
              (* XXX: Should actually check that types match too... *)
              (* Fill the hole with the given value and run in the
                 continuation (closure)'s environment.
               *)
              k eta ctx v2
            else
              Error.runtime ~loc "Context length mismatch in eval-kapp"

        | I.VTerm b1, I.VTerm b2 ->
            begin
              let t1 = Typing.type_of ctx b1  in
              match Equal.whnf_ty ~use_rws:true ctx t1 with
              | Syntax.Prod(x,t,u), _ ->
                  begin
                    let t2 = Typing.type_of ctx b2 in
                    sequence
                      (function
                        | I.VInj(1, (I.VTuple ws, _)), _ ->
                            let ctx' = extend_context_with_witnesses ctx ws in
                            if Equal.equal_ty ctx' t t2 then
                              (* XXX Add the witnesses to the term!!! *)
                              I.RVal (I.mkVTerm (Syntax.App((x,t,u),b1,b2), loc))
                            else
                              Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
                        | v' ->  Error.runtime ~loc "Bad mkApp. Why is@ %t@ == %t ? (%s)"
                                 (print_ty ctx t) (print_ty ctx t2) (I.string_of_value ctx v')
                      )
                      (equiv_ty ctx env t t2)
                  end
              | _ -> Error.runtime ~loc "Can't prove operator in application is a product"
            end

        | _, _ -> Error.runtime ~loc "Bad application"
      end

  | I.Let(pat,c1,c2) ->
      begin
        let r = run ctx env c1  in
        sequence (fun v ->
                    let env' =
                      (try insert_matched ctx env (v,pat)
                       with
                        | NoPatternMatch ->
                           Error.runtime ~loc "let pattern-match failed") in
                    run ctx env' c2) r
      end

(*
  | I.LetRec(defs,c2) ->
      let env =
        let env' = ref env in
        let env = List.fold_right
          (fun (f, (x,c)) env ->
             let g = I.VFun((fun env ctx v -> run ctx (insert_ttvar x v ctx env) c), env ), loc

             V.Closure (fun v -> ceval (extend p v !env') c) in
             insert_ttvar f g env)
          defs env in
        env' := env;
        env

      begin
        let r = run ctx env c1  in
        sequence (fun v -> run ctx (insert_ttvar x v ctx env) c2) r
      end
      *)

    | I.Match(e, arms) ->
        let v = eval ctx env e  in
        let rec find_match = function
          | []             -> Error.runtime ~loc "No matching pattern found"
          |  (pat,c)::arms ->
              begin
                try
                  insert_matched ctx env (v,pat), c
                with
                  | NoPatternMatch -> find_match arms
              end  in
        let env', c = find_match arms  in
        run ctx env' c

    | I.Op(tag, e) ->
      (* eval-op *)
      let v = eval ctx env e  in
      I.ROp(tag, Context.empty, v, ((fun _ _ v -> I.RVal v), env))

    | I.WithHandle(e,c) ->
        begin
          let h = eval ctx env e  in
          let r = run ctx env c  in
          match fst h with
          | I.VHandler (hfun,eta)  ->
              hfun eta ctx r
          | _ ->
              Error.runtime ~loc "Non-handler expression given to with/handle"
        end

    | I.MkVar i ->
        let vars = depth ctx  in
        if i < vars then
          I.RVal (I.mkVTerm ~loc (Syntax.Var i, loc))
        else
          Error.runtime ~loc "Index is %d but context has length %d" i vars

    | I.MkLam (x1, e2, c3) ->
        begin
          let domain =
          match eval ctx env e2 with
            | I.VType t2, _ -> t2
            | I.VTerm b, _ ->
                 begin
                   let t = Typing.type_of ctx b  in
                   match Equal.as_universe ctx t with
                   | Some alpha -> Syntax.El(alpha, b), snd e2
                   | None -> Error.runtime ~loc
                              "Bad type annotation in lambda.@ Why does %t belong to a universe?"
                              (print_term ctx b)
                 end
            | v2 -> Error.runtime ~loc "Bad type annotation in lambda; found %s"
                         (I.string_of_value ~brief:false ctx v2)   in

          let ctx' = Context.add_var x1 domain ctx  in
          let r3 = run ctx' env c3  in
          sequence ~withdelta:(x1,domain) (fun v3 -> I.RVal (abstract ctx' x1 domain v3)) r3
        end

    | I.Check(t1, t2, e, c) ->
        begin
          match eval ctx env e  with
          | I.VTuple ws, _ ->
              let ctx' = extend_context_with_witnesses ctx ws in
              if Equal.equal_ty ctx' t1 t2 then
                run ctx' env c (* Run the body with the added hints *)
              else
                Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
          | _, _ -> Error.runtime ~loc "Evidence in Check was not a tuple"
        end


    | I.Ascribe(e1, e2) ->
        begin
          match eval ctx env e1, eval ctx env e2 with
          | (I.VTerm b, _), (I.VType t, _) ->
              begin
                let u = Typing.type_of ctx b  in
                sequence
                  (function
                    | I.VInj(1, (I.VTuple ws, _)), _ ->
                        let ctx' = extend_context_with_witnesses ctx ws in
                        if Equal.equal_ty ctx' t u then
                          I.RVal
                               (I.mkVTerm (wrap_syntax_with_witnesses ctx
                                             (Syntax.Ascribe(b,t), Position.nowhere) ws ))
                        else
                          Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
                    | _ ->
                        Error.runtime ~loc "Brazil could not produce witnesses for the ascription"
                  )
                 (equiv_ty ctx env t u)
              end

          | (I.VTerm _, _), _ -> Error.runtime ~loc "Non-type in ascribe"
          | _,              _ -> Error.runtime ~loc "Non-term in ascribe"
        end

    | I.RunML (f, e) ->
        let v = eval ctx env e in
        f ctx env v


and vok env exp =
  (* XXX *)
  true





and equiv_ty ctx env t u =
  if Syntax.equal_ty t u then
    retSomeTuple []
  else
    match Syntax.name_of t, Syntax.name_of u with
    | Some (e_t, alpha), Some (e_u, beta) ->
        begin
          if Universe.eq alpha beta then
            equiv ctx env e_t e_u (Syntax.Universe alpha, Position.nowhere)
          else
            (Print.debug "Unequal universes in equiv_ty!";
             retNone)
        end
    | _, _ ->
        Error.runtime "equiv_ty couldn't find the name of a type!"

and equiv ctx env term1 term2 t =

  Print.debug "equiv: %t == %t @@ %t"
    (print_term ctx term1) (print_term ctx term2) (print_ty ctx t);

  if (Syntax.equal term1 term2) then
    retSomeTuple []
  else
    let userCmd =
      I.mkApp (I.mkVar "equiv")
              (I.mkTuple [ I.mkTerm term1 ; I.mkTerm term2 ; I.mkType t ])  in
    run ctx env userCmd

let toplevel_handler =
  let k = "toplevel k" in
  let continue_with_unit = I.mkApp (I.mkVar k) (I.mkConst I.Unit)  in
  let doPrint ctx ttenv v =
    (Format.printf "%s@." (I.string_of_value ~brief:true ctx v);
     Print.debug "finished printing, I hope";
     I.RVal (I.mkVConst I.Unit))  in
  {
    I.valH = None ;
    I.opH  = [ ("equiv", I.PWild, k, continue_with_unit);
               ("print", I.PVar "x", k, I.mkLet I.PWild (I.mkRunML doPrint (I.mkVar "x"))
                                          continue_with_unit) ;
             ] ;

    I.finH = None ;
  }

let rec toprun ctx env c =
  let c' = I.mkWithHandle (I.mkHandler toplevel_handler) c in
  run ctx env c'

