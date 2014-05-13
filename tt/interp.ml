module I = InputTT
module SM = InputTT.StringMap

type env =
  {
    ctx : Context.t;
    ttenv : I.environment;
  }

let empty_env =
  {
    ctx = Context.empty;
    ttenv = SM.empty;
  }

let depth env =
  List.length (Context.names env.ctx)

let insert_ttvar x v env =
  let current_depth = depth env in
  { env with ttenv = SM.add x (v,current_depth) env.ttenv }


(********************)
(* Helper Functions *)
(********************)

(* Printing *Syntax* types and terms *)

let print_ty env ty =
  Print.ty (Context.names env.ctx) ty

let print_term env term =
  Print.term (Context.names env.ctx) term

let print_universe = Print.universe

let string_of_env env =
        let current_depth = depth env in
  "[" ^ String.concat "," (List.map (fun (k,(v,i)) -> k^"="^(I.string_of_value
  env.ctx (I.shiftv 0 (current_depth - i) v))) (SM.bindings env.ttenv)) ^ "]"

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


(********************)
(* Pattern-Matching *)
(********************)

exception NoPatternMatch

(* [insert_matched env (v,pat)] either inserts the TT values from [v] where there
   are corresponding variables in [pat], or raises the [NoPatternMatch]
   exception if [pat] and [v] don't have the same form.
 *)
let rec insert_matched env (v,pat) =
  match fst v, pat with
  | _,             I.PWild    -> env
  | _,             I.PVar x   -> insert_ttvar x v env
  | I.VConst a1,   I.PConst a2    when a1 = a2  ->  env
  | I.VInj(i1,v1), I.PInj (i2,p2) when i1 = i2  ->  insert_matched env (v1, p2)
  | I.VTuple vs,   I.PTuple ps    when List.length vs = List.length ps ->
      List.fold_left insert_matched env (List.combine vs ps)
  | I.VType (Syntax.Id(_,b1,b2),loc), I.PJuEqual(pat1, pat2) ->
      List.fold_left insert_matched env [I.mkVTerm ~loc b1,pat1; I.mkVTerm ~loc b2,pat2]
  | _, (I.PConst _ | I.PInj _ | I.PTuple _
        | I.PJuEqual _) -> raise NoPatternMatch


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

(**************************)
(* Evaluating Expressions *)
(**************************)

(* [eval env e] deterministically reduces TT expression [e] to a
   value, without side-effects. This largely involves looking up
   variables in the environment, and building closures.
 *)
let rec eval env (exp', loc) =
  match exp' with
  | I.Value v   -> v
  | I.Var x ->
      if SM.mem x env.ttenv then
        let (value, insert_depth) = SM.find x env.ttenv  in
        let current_depth = depth env in
        let delta = current_depth - insert_depth in
        assert (delta >= 0);
        I.shiftv 0 delta value
      else
        Error.runtime ~loc "Undefined variable %s" x
  | I.Const a   -> I.VConst a, loc
  | I.Term b    -> I.VTerm b, loc
  | I.Type t    -> I.VType t, loc
  | I.Fun (x,c) -> I.VFun(fun v -> run (insert_ttvar x v env) c), loc
  | I.Handler h -> I.VHandler (eval_handler env loc h), loc
  | I.Tuple es  -> I.VTuple (List.map (eval env) es), loc
  | I.Inj(i,e)  -> I.VInj(i, eval env e), loc
  | I.Prim(op, es) -> eval_prim env loc op (List.map (eval env) es)


and eval_prim env loc op vs =
    match op, vs with
    | I.Not, [I.VConst(I.Bool b), _]  -> I.mkVConst(I.Bool (not b))
    | I.And, [I.VConst(I.Bool b1), _;
              I.VConst(I.Bool b2), _] -> I.mkVConst(I.Bool (b1 && b2))
    | I.Plus, [I.VConst(I.Int n1), _;
               I.VConst(I.Int n2), _] -> I.mkVConst(I.Int (n1 + n2))
    | I.Append, [I.VTuple es1, _;
                 I.VTuple es2, _]     -> I.mkVTuple (es1 @ es2)
    | I.Eq,  [a1; a2] -> I.mkVConst( I.Bool (     I.eqvalue a1 a2))
    | I.Neq, [a1; a2] -> I.mkVConst( I.Bool (not (I.eqvalue a1 a2)))
    | I.Whnf, [I.VTerm b, _] ->
        let t = Typing.type_of env.ctx b  in
        I.mkVTerm (Equal.whnf ~use_rws:true env.ctx t b)
    | I.Whnf, [I.VType t, _] ->
        I.mkVType (Equal.whnf_ty ~use_rws:true env.ctx t)

    | _, _ -> Error.runtime ~loc "Bad arguments to primitive"


and eval_handler env loc {I.valH; I.opH; I.finH} =
  let rec hfun = function
    | I.RVal v ->
        begin
          Print.debug "Handler %s produced value %s@." (Position.to_string loc) (I.string_of_value env.ctx v);
          match valH with
          | Some (xv,cv) ->
              (* eval-handle-val *)
              run (insert_ttvar xv v env) cv
          | None ->
              I.RVal v
        end

    | I.ROp (opi, delta, v, k) ->
        begin
          Print.debug "Handler produced operation %s@." opi;

          let k' u = hfun (k u)  in
          let rec loop = function
            | [] ->
                (Print.debug "No matching case found for body %s@." (Position.to_string loc);
                I.ROp(opi, delta, v, k'))
            | (op, pat, kvar, c)::rest when op = opi ->
                begin
                  try
                    Print.debug "Found matching case %s. Creating VCont with env =
                      %s" op (string_of_env env);
                    let kval = I.mkVCont env.ctx delta k' in
                    let env_h = { env with ctx = Context.append env.ctx delta }  in
                    let env_h = insert_matched env_h (v,pat) in
                    let env_h = insert_ttvar kvar kval env_h  in
                    match run env_h c with
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
       fun r ->
         begin
           match finH with
           | None -> hfun r
           | Some (xf,cf) ->
               sequence (fun v -> run (insert_ttvar xf v env) cf) (hfun r)
         end




(*************************)
(* Running a Computation *)
(*************************)

and sequence k = function
  | I.RVal v -> k v
  | I.ROp(tag,delta,v,k') ->
      let k'' u = sequence k (k' u)  in
      I.ROp(tag,delta,v,k'')

and run (env : env) (comp, loc) =
  Print.debug "run: %s\n%s" (I.string_of_computation env.ctx (comp,loc))
  (string_of_env env);

  match comp with

  | I.Return e  ->
      I.RVal (eval env e)

  | I.App (e1, e2) ->
      begin
        Print.debug "App. env = %s@." (string_of_env env);
        let v1 = eval env e1  in
        let v2 = eval env e2  in
        Print.debug "v1 = %s, v2 = %s@." (I.string_of_value env.ctx v1)
        (I.string_of_value  env.ctx v2);
        match fst v1, fst v2 with

        | I.VFun f, _ ->
            (* Extend _closure_ environment with argument
               and run the function body
             *)
            f v2

        | I.VCont(gamma,delta,k), _ ->
            (* eval-kapp *)
            Print.debug "Applying vcont. env = %s@." (string_of_env env);
            if (List.length (Context.names env.ctx) =
                List.length (Context.names gamma) + List.length (Context.names delta)) then
              (* XXX: Should actually check that types match too... *)
              (* Fill the hole with the given value and run in the
                 continuation (closure)'s environment.
               *)
              k v2
            else
              Error.runtime ~loc "Context length mismatch in eval-kapp"

        | I.VTerm b1, I.VTerm b2 ->
            begin
              let t1 = Typing.type_of env.ctx b1  in
              match Equal.whnf_ty ~use_rws:true env.ctx t1 with
              | Syntax.Prod(x,t,u), _ ->
                  begin
                    let t2 = Typing.type_of env.ctx b2 in
                    match equiv_ty env t t2 with
                    | I.RVal (I.VInj(1, (I.VTuple ws, _)), _) ->
                        let ctx' = extend_context_with_witnesses env.ctx ws in
                        if Equal.equal_ty ctx' t t2 then
                          I.RVal (I.mkVTerm (Syntax.App((x,t,u),b1,b2), loc))
                        else
                          Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
                    | _ -> Error.runtime ~loc "Bad mkApp. Why is@ %t@ == %t ?"
                             (print_ty env t) (print_ty env t2)

                  end
              | _ -> Error.runtime ~loc "Can't prove operator in application is a product"
            end

        | _, _ -> Error.runtime ~loc "Bad application"
      end

  | I.Let(x,c1,c2) ->
      begin
        let r = run env c1  in
        sequence (fun v -> run (insert_ttvar x v env) c2) r
      end

    | I.Match(e, arms) ->
        let v = eval env e  in
        let rec find_match = function
          | []             -> Error.runtime ~loc "No matching pattern found"
          |  (pat,c)::arms ->
              begin
                try
                  insert_matched env (v,pat), c
                with
                  | NoPatternMatch -> find_match arms
              end  in
        let env', c = find_match arms  in
        run env' c

    | I.Op(tag, e) ->
      (* eval-op *)
      let v = eval env e  in
      I.ROp(tag, Context.empty, v, (fun v -> I.RVal v))

    | I.WithHandle(e,c) ->
        begin
          let h = eval env e  in
          let r = run env c  in
          match fst h with
          | I.VHandler hfun  ->
              hfun r
          | _ ->
              Error.runtime ~loc "Non-handler expression given to with/handle"
        end

    | I.MkVar i ->
        let vars = depth env  in
        if i < vars then
          I.RVal (I.mkVTerm ~loc (Syntax.Var i, loc))
        else
          Error.runtime ~loc "Index is %d but context has length %d" i vars

    | I.MkLam (x1, e2, c3) ->
        begin
          match eval env e2 with
          | I.VType t2, _ ->
              begin
                let env' = {env with ctx = Context.add_var x1 t2 env.ctx }  in
                let r3 = run env' c3  in
                sequence (fun v3 -> I.RVal (abstract env'.ctx x1 t2 v3)) r3
              end
          | _, _ -> Error.runtime ~loc "Annotation in MkLam is not a type"
        end

    | I.Check(t1, t2, e, c) ->
        begin
          match eval env e  with
          | I.VTuple ws, _ ->
              let ctx' = extend_context_with_witnesses env.ctx ws in
              if Equal.equal_ty ctx' t1 t2 then
                run {env with ctx = ctx'} c (* Run the body with the added hints *)
              else
                Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
          | _, _ -> Error.runtime ~loc "Evidence in Check was not a tuple"
        end


    | I.Ascribe(e1, e2) ->
        begin
          match eval env e1, eval env e2 with
          | (I.VTerm b, _), (I.VType t, _) ->
              begin
                let u = Typing.type_of env.ctx b  in
                match equiv_ty env t u with
                | I.RVal (I.VInj(1, (I.VTuple ws, _)), _) ->
                    I.RVal
                         (I.mkVTerm (wrap_syntax_with_witnesses env.ctx
                                       (Syntax.Ascribe(b,t), Position.nowhere) ws ))

                | _ -> Error.runtime ~loc "Brazil cannot prove the ascription valid"
              end

          | (I.VTerm _, _), _ -> Error.runtime ~loc "Non-type in ascribe"
          | _,              _ -> Error.runtime ~loc "Non-term in ascribe"
        end

    | I.BrazilTermCode text ->
        begin
          let term = parse_literal Parser.topterm loc text  in
          let term = Debruijn.term (Context.names env.ctx) term in
          let term, _ty = Typing.syn_term env.ctx term  in
          I.RVal (I.mkVTerm ~loc term)
        end

    | I.BrazilTypeCode text ->
        begin
          let term = parse_literal Parser.topty loc text  in
          let ty = Debruijn.ty (Context.names env.ctx) term in
          let ty = Typing.is_type env.ctx ty  in
          I.RVal (I.mkVType ~loc ty)
        end

    | I.RunML (f, e) ->
        let v = eval env e in
        f env.ctx env.ttenv v


and vok env exp =
  (* XXX *)
  true





and equiv_ty env t u =
  if Syntax.equal_ty t u then
    retSomeTuple []
  else
    match Syntax.name_of t, Syntax.name_of u with
    | Some (e_t, alpha), Some (e_u, beta) ->
        begin
          if Universe.eq alpha beta then
            equiv env e_t e_u (Syntax.Universe alpha, Position.nowhere)
          else
            (Print.debug "Unequal universes in equiv_ty!";
             retNone)
        end
    | _, _ ->
        Error.runtime "equiv_ty couldn't find the name of a type!"

and equiv env term1 term2 t =

  Print.debug "equiv: %t == %t @@ %t"
    (print_term env term1) (print_term env term2) (print_ty env t);

  if (Syntax.equal term1 term2) then
    retSomeTuple []
  else
    let userCmd =
      I.mkApp (I.mkVar "equiv")
              (I.mkTuple [ I.mkTerm term1 ; I.mkTerm term2 ; I.mkType t ])  in
    match run env userCmd with
    | I.RVal (I.VInj(1, (I.VTuple ws, _)), _) ->
         let ctx' = extend_context_with_witnesses env.ctx ws in
         if (Equal.equal_term {Equal.use_eqs = true; Equal.use_rws = true} ctx' term1 term2 t) then
           retSomeTuple ws
         else
           Error.runtime "Insufficient witnesses for equivalence"

    | _ -> retNone


let toplevel_handler =
  let k = "toplevel k" in
  let continue_with_unit = I.mkApp (I.mkVar k) (I.mkConst I.Unit)  in
  let doPrint ctx ttenv v =
    (print_endline (I.string_of_value ~brief:true ctx v); I.RVal (I.mkVConst I.Unit))  in
  {
    I.valH = None ;
    I.opH  = [ ("equiv", I.PWild, k, continue_with_unit);
               ("print", I.PVar "x", k, I.mkLet "_" (I.mkRunML doPrint (I.mkVar "x"))
                                          continue_with_unit) ;
             ] ;

    I.finH = None ;
  }

let rec toprun env c =
  let c' = I.mkWithHandle (I.mkHandler toplevel_handler) c in
  run env c'

