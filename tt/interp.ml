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

let insert_ttvar x v env =
  let current_depth = List.length (Context.names env.ctx) in
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

(* Gensym *)

let fresh_name =
  let counter = ref 0 in
  fun () -> (let n = !counter in
             let _ = incr counter in
             "X$" ^ string_of_int n)




let lambdaize env x t =
  let ctx' = Context.add_var x t env.ctx in
  let rec loop = function
    | I.VTerm body, loc ->
        I.VTerm (Syntax.Lambda(x, t, Typing.type_of ctx' body, body), loc), loc
    | I.VTuple es, loc ->
        I.VTuple (List.map loop es), loc
    | (_, loc) -> Error.runtime ~loc "Bad body to MkLam"  in
  loop



(* [firstSome lst ] takes a list of [lazy] thunks returning ['a option]s. If any
   is [Some x] then the answer is [Some x] and no following thunks are forced).
   If all thunks return None, the final answer is [None].
*)
let rec firstSome = function
  | [] -> Error.runtime "firstSome called with no thunks"
  | [lazy thunkResult] -> thunkResult
  | (lazy thunkResult) :: thunks ->
    begin
      match thunkResult with
      | None -> firstSome thunks
      | Some answer -> Some answer
    end


let rec joinSome = function
  | [] -> Error.runtime "joinSome called with no thunks"
  | [lazy thunkresult] -> thunkresult
  | (lazy thunkresult) :: thunks ->
    begin
      match thunkresult with
      | None -> None
      | Some firstAnswers ->
        begin
          match joinSome thunks with
          | None -> None
          | Some restAnswers ->  Some (firstAnswers @ restAnswers)
        end
    end

let extend_context_with_witnesses ctx0 =
  let rec loop = function
    | [] -> ctx0
    | w::ws ->
        begin
          match fst w with
          | I.VTerm b -> Context.add_equation b (Typing.type_of ctx0 b) (loop ws)
          | _ -> Error.runtime "Witness %s is not a term" (I.string_of_value ctx0 w)
        end  in
  loop

let wrap_syntax_with_witnesses ctx0 e =
  let rec loop = function
    | [] -> e
    | w::ws ->
        begin
          match fst w with
          | I.VTerm b -> Syntax.Equation(b, Typing.type_of ctx0 b, loop ws), Position.nowhere
          | _ -> Error.runtime "Witness %s is not a term" (I.string_of_value ctx0 w)
        end  in
  loop

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
        let current_depth = List.length (Context.names env.ctx) in
        let delta = current_depth - insert_depth in
        assert (delta >= 0);
        I.shiftv 0 delta value
      else
        Error.runtime ~loc "Undefined variable %s" x
  | I.Const a   -> I.VConst a, loc
  | I.Term b    -> I.VTerm b, loc
  | I.Type t    -> I.VType t, loc
  | I.Fun (x,c) -> I.VFun(x, c, env.ttenv), loc
  | I.Handler h -> I.VHandler (h, env.ttenv), loc
  | I.Tuple es  -> I.VTuple (List.map (eval env) es), loc
  | I.Inj(i,e)  -> I.VInj(i, eval env e), loc

(********************)
(* Pattern-Matching *)
(********************)

exception NoPatternMatch

(* [extend_match env (v,pat)] either inserts the TT values from [v] where there
   are corresponding variables in [pat], or raises the [NoPatternMatch]
   exception if [pat] and [v] don't have the same form.
 *)
let rec extend_match env (v,pat) =
  match fst v, pat with
  | _,             I.PWild    -> env
  | _,             I.PVar x   -> insert_ttvar x v env
  | I.VConst a1,   I.PConst a2    when a1 = a2  ->  env
  | I.VInj(i1,v1), I.PInj (i2,p2) when i1 = i2  ->  extend_match env (v1, p2)
  | I.VTuple vs,   I.PTuple ps    when List.length vs = List.length ps ->
      List.fold_left extend_match env (List.combine vs ps)
  | _, _ -> raise NoPatternMatch


let rec run (env : env) (comp, loc) =
  Print.debug "%s" (I.string_of_computation env.ctx (comp,loc));
  match comp with

  | I.Return e  ->
      I.RVal (eval env e)

  | I.App (e1, e2) ->
      begin
        let v1 = eval env e1  in
        let v2 = eval env e2  in
        match fst v1, fst v2 with

        | I.VFun (x,c,eta), _ ->
            (* Extend _closure_ environment with argument
               and run the function body
             *)
            run (insert_ttvar x v2 { env with ttenv = eta }) c

        | I.VCont(gamma,delta,k,eta), _ ->
            (* eval-kapp *)
            if (List.length (Context.names env.ctx) =
                List.length (Context.names gamma) + List.length (Context.names delta)) then
              (* XXX: Should actually check that types match too... *)
              (* Fill the hole with the given value and run in the
                 continuation (closure)'s environment.
               *)
              run {env with ttenv = eta} (I.kfill v2 k)
            else
              Error.runtime ~loc "Context length mismatch in eval-kapp"

        | I.VTerm b1, I.VTerm b2 ->
            begin
              let t1 = Typing.type_of env.ctx b1  in
              match Typing.whnfs_ty env.ctx t1 with
              | Syntax.Prod(x,t,u), _ ->
                  begin
                    let t2 = Typing.type_of env.ctx b2 in
                    match equiv_ty env t t2 with
                    | Some ws ->
                        let ctx' = extend_context_with_witnesses env.ctx ws in
                        if Typing.equiv_ty ctx' t t2 then
                          I.RVal (I.mkVTerm (Syntax.App((x,t,u),b1,b2), loc))
                        else
                          Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
                    | None -> Error.runtime ~loc
                      "Bad mkApp. Why is@ %t@ == %t ?" (print_ty env t) (print_ty env t2)

                  end
              | _ -> Error.runtime ~loc "Can't prove operator in application is a product"
            end

        | _, _ -> Error.runtime ~loc "Bad application"
      end

  | I.Let(x,c1,c2) ->
      begin
        match run env c1 with

        | I.RVal v ->
            (* eval-let-val *)
            run (insert_ttvar x v env) c2

        | I.ROp(op, delta, v, (k,eta)) ->
            (* eval-let-op *)
            I.ROp(op, delta, v, (I.KLet(x,k,c2), eta))
            (* Justify moving c2 into eta *)
      end

    | I.Match(e, arms) ->
        let v = eval env e  in
        let rec loop = function
          | [] -> Error.runtime ~loc "No matching pattern found"
          |  (pat,c)::arms ->
              begin
                try
                  extend_match env (v,pat), c
                with
                  | NoPatternMatch -> loop arms
              end  in
        let env', c = loop arms  in
        run env' c

    | I.Op(tag, e) ->
      (* eval-op *)
      let v = eval env e  in
      I.ROp(tag, Context.empty, v, (I.KHole, env.ttenv))

    | I.WithHandle(e,c) ->
        begin
          let h = eval env e  in
          match fst h with
          | I.VHandler ({I.valH; I.opH; I.finH=None}, eta_h)  ->
              begin
                match run env c with

                | I.RVal v ->
                    begin
                      Print.debug "Handler body produced value %s@." (I.string_of_value env.ctx v);
                      match valH with
                      | Some (xv,cv) ->
                          (* eval-handle-val *)
                          run (insert_ttvar xv v {env with ttenv = eta_h})  cv
                      | None ->
                          I.RVal v
                    end

                | I.ROp (opi, delta, v, (k1,eta1)) as r ->
                    begin
                      Print.debug "Handler body produced operation %s@." opi;
                      let env' = {
                                  ctx = Context.append env.ctx delta ;
                                  ttenv = eta_h ;
                                 }  in
                      let k1' = I.mkVCont env.ctx delta (I.KWithHandle(I.mkValue h, k1)) eta1  in

                      let handler_result =
                        let rec loop = function
                          | [] ->
                              r
                          | (op, pat, kvar, c)::rest when op = opi ->
                              begin
                                try
                                  let env'' = extend_match env' (v,pat) in
                                  let env'' = insert_ttvar kvar k1' env''  in
                                  run env'' c
                                with
                                  | NoPatternMatch -> loop rest
                              end
                          | _ :: rest -> loop rest  in

                        loop opH   in

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
         | I.VHandler ({I.finH=Some (xf,cf)} as h, eta_h) ->
             let h' = { h with I.finH = None }  in
             run env (I.Let(xf, (I.WithHandle(I.mkValue (I.mkVHandler h' eta_h),c),loc), cf), loc)
         | _ ->
              Error.runtime ~loc "Non-handler expression given to with/handle"
        end

    | I.MkVar n ->
        (* eval-make-var *)
        let nvars = List.length (Context.names env.ctx)  in
        if nvars > n then
          I.RVal (I.VTerm (Syntax.Var n, loc), loc)
        else
          Error.runtime ~loc "Index is %d but context has length %d" n nvars

    | I.MkLam (x1, e2, c3) ->
        begin
          let v2 = eval env e2  in
          match fst v2 with
          | I.VType t2 ->
              begin
                let env' = {env with ctx = Context.add_var x1 t2 env.ctx }  in
                match (run env' c3) with
                | I.RVal v3 ->
                    (* eval-make-lambda-val *)
                    (* eval-make-lambda-val-tuple *)
                    I.RVal (lambdaize env x1 t2 v3)
                | I.ROp (op, delta, e, (k, eta)) ->
                    (* eval-make-lambda-op *)
                    let delta0 = Context.add_var x1 t2 Context.empty in
                    I.ROp (op, Context.append delta0 delta, e, (I.KMkLam(x1, t2, k), eta))
              end
          | _ -> Error.runtime ~loc "Annotation in MkLam is not a type"
        end

    | I.Check(t1, t2, e, c) ->
        begin
          (* eval-assert-type *)
          let v = eval env e  in
          match fst v with
          | I.VTuple ws ->
              let rec loop = function
                | [] -> env.ctx
                | w::ws ->
                    begin
                      match fst w with
                      | I.VTerm b -> Context.add_equation b (Typing.type_of env.ctx b) (loop ws)
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
          let vs = List.map (eval env) es  in
          let answer =
            match op, vs with
            | I.Not, [I.VConst(I.Bool b), _] -> I.mkVConst(I.Bool (not b))
            | I.And, [I.VConst(I.Bool b1), _; I.VConst(I.Bool b2), _] ->
                  I.mkVConst(I.Bool (b1 && b2))
            | I.Plus, [I.VConst(I.Int n1), _; I.VConst(I.Int n2), _] ->
                  I.mkVConst(I.Int (n1 + n2))
            | I.Append, [I.VTuple es1, _; I.VTuple es2, _] ->
                  I.mkVTuple (es1 @ es2)
            | _, _ -> Error.runtime ~loc "Bad arguments to primitive"  in
          I.RVal answer
        end

    | I.Ascribe(e1, e2) ->
        begin
          let v1 = eval env e1  in
          let v2 = eval env e2  in
          match fst v1, fst v2 with
          | I.VTerm b, I.VType t ->
              begin
                let u = Typing.type_of env.ctx b  in
                match equiv_ty env t u with
                | Some ws ->
                    I.RVal
                     (I.mkVTerm
                      (wrap_syntax_with_witnesses env.ctx
                           (Syntax.Ascribe(b,t), Position.nowhere) ws ))

                | None ->
                    Error.runtime ~loc "Cannot prove ascription valid"
              end
          | I.VTerm _, _ -> Error.runtime ~loc "Non-type in ascribe"
          | _, _ -> Error.runtime ~loc "Non-term in ascribe"
        end

    | I.BrazilTermCode text ->
        begin
          let lexbuf = Lexing.from_string text in
          let term =
             try
                Parser.topterm Lexer.token lexbuf
             with
              | Parser.Error ->
                  Error.syntax ~loc:(Position.of_lex lexbuf) "Brazil code at %s" (Position.to_string loc)
              | Failure "lexing: empty token" ->
                  Error.syntax ~loc:(Position.of_lex lexbuf) "unrecognised symbol in Brazil literal at %s." (Position.to_string loc)   in
          let term = Debruijn.term (Context.names env.ctx) term in
          let term, _ty = Typing.syn_term env.ctx term  in
          I.RVal (I.VTerm term, loc)
        end

    | I.BrazilTypeCode text ->
        begin
          let lexbuf = Lexing.from_string text in
          let term =
             try
                Parser.topty Lexer.token lexbuf
             with
              | Parser.Error ->
                  Error.syntax ~loc:(Position.of_lex lexbuf) "Brazil code at %s" (Position.to_string loc)
              | Failure "lexing: empty token" ->
                  Error.syntax ~loc:(Position.of_lex lexbuf) "unrecognised symbol in Brazil literal at %s." (Position.to_string loc)   in
          let ty = Debruijn.ty (Context.names env.ctx) term in
          let ty = Typing.is_type env.ctx ty  in
          I.RVal (I.VType ty, loc)
        end


and eok env exp =
  (* XXX *)
  true


(* Adapted from brazil/typing.ml and the original src/equivalence.ml *)

and equiv_ty env t u =
  if Syntax.equal_ty t u then
    Some []
  else
    match Syntax.name_of t, Syntax.name_of u with
    | Some (e_t, alpha), Some (e_u, beta) ->
        begin
          if Universe.eq alpha beta then
            equiv env e_t e_u (Syntax.Universe alpha, Position.nowhere)
          else
            (Print.debug "Unequal universes in equiv_ty!";
             None)
        end
    | _, _ ->
        Error.runtime "equiv_ty couldn't find the name of a type!"

and equiv env term1 term2 t =

  Print.debug "equiv: %t == %t @@ %t"
    (print_term env term1) (print_term env term2) (print_ty env t);

  firstSome
  [
    lazy ( if (Syntax.equal term1 term2) then Some [] else None ) ;

    lazy ( let userCmd =
             I.mkOp "equiv"
                    (I.mkTuple
                      [ I.mkTerm term1 ;
                        I.mkTerm term2 ;
                        I.mkType t ;
                      ])  in
             match run env userCmd with
             | I.RVal (I.VInj(1, (I.VTuple ws, _)), _) ->
                 let ctx' = extend_context_with_witnesses env.ctx ws in
                 if (Typing.equiv ctx' term1 term2 t) then
                   Some ws
                 else
                   Error.runtime "Insufficient witnesses for equivalence"

             | _ -> None ) ;
(*
    lazy ( let t' = Typing.whnfs_ty env.ctx t in
           equiv_ext env term1 term2 t' ) ;
           *)
  ]

and equiv_ext env ((_, loc1) as e1) ((_, loc2) as e2) ((ty', _) as ty) =
  begin
    Print.debug "equiv_ext: %t == %t @@ %t @."
      (print_term env e1) (print_term env e2) (print_ty env ty);

    match ty' with

    (* chk-eq-ext-prod *)
    | Syntax.Prod(x, t, u) ->
        (* To keep the two x binders straight, we'll call the one in
           the context z. *)
        let ctx' = Context.add_var x t env.ctx  in   (* ctx' === ctx, z *)
                                           (* ctx       |- e1  : ... *)
        let e1' = Syntax.weaken 0 e1 in    (* ctx, z    |- e1' : ... *)
                                           (* ctx       |- e2  : ... *)
        let e2' = Syntax.weaken 0 e2 in    (* ctx, z    |- e2' : ... *)
                                           (* ctx       |- t  type *)
        let t'  = Syntax.weaken_ty 0 t in  (* ctx, z    |- t' type *)
                                           (* ctx,    x |- u type *)
        let u' = Syntax.weaken_ty 1 u  in  (* ctx, z, x |- u type *)
        let z = (Syntax.Var 0,
                 Position.nowhere) in      (* ctx, z    |- z : ... *)
        equiv {env with ctx = ctx'}
              (Syntax.App((x, t', u'), e1', z), loc1)
              (Syntax.App((x, t', u'), e2', z), loc2)
              u'

    (* chk-eq-ext-unit *)
    | Syntax.Unit ->
        Some []

    (* chk-eq-ext-K *)
    | Syntax.Id (_T, _e3, _e4) ->
        Some []

    (* chk-eq-ext-whnf *)
    | _ ->
        let e1' = Typing.whnfs env.ctx e1 ty in
        let e2' = Typing.whnfs env.ctx e2 ty in
        equiv_whnf env e1' e2' ty
  end

and equiv_whnf env ((term1', loc1) as term1) ((term2', _loc2) as term2) ty =
  begin
    match term1', term2' with

    (* chk-eq-whnf-reflexivity *)
    | _, _ when Syntax.equal term1 term2 ->
        Some []

    (* chk-eq-whnf-equation *)
    | _, _ when Context.lookup_equation ty term1 term2 env.ctx ->
        Some []

    (* Subsumed by reflexivity
    | Syntax.Var index1, Syntax.Var index2 ->
        if ( index1 = index2 ) then Some [] else None
    *)

    (* chk-eq-whnf-app *)
    | Syntax.App((x, t1, t2), e1, e2), Syntax.App((_, u1, u2), e1', e2') ->
        joinSome
        [ lazy ( equiv_ty env t1 u1 ) ;
          lazy ( equiv_ty {env with ctx = Context.add_var x t1 env.ctx} t2 u2 ) ;
          lazy ( equiv_whnf env e1 e1' (Syntax.Prod (x, t1, t2), loc1) ) ;
          lazy ( equiv env e2 e2' t1 ) ;
        ]

    (* chk-eq-whnf-idpath *)
    | Syntax.Idpath(t, e1), Syntax.Idpath(u, e2) ->
        joinSome
        [
          lazy ( equiv_ty env t u ) ;
          lazy ( equiv env e1 e2 t ) ;
        ]



    (* chk-eq-whnf-j *)
    | Syntax.J(t1,(x,y,p,u2),(z,e3),e4, e5, e6), Syntax.J(t7, (_,_,_,u8), (_,e9), e10, e11, e12) ->
        let ctx_xy = Context.add_vars
                       [  (x, t1);
                          (y, t1); ] env.ctx in
        let ctx_xyp = Context.add_vars
                       [  (p, (Syntax.Paths
                                (Syntax.shift_ty 2 t1,  (* Weaken twice for x and y *)
                                (Syntax.Var 0 (* x *), Position.nowhere),
                                (Syntax.Var 1 (* y *), Position.nowhere)),
                                Position.nowhere)) ] ctx_xy  in
        let ctx_z = Context.add_var z t1 env.ctx  in

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

        joinSome
        [
          lazy ( equiv_ty env t1 t7 ) ;
          lazy ( equiv_ty {env with ctx = ctx_xyp} u2 u8 ) ;
          lazy ( equiv {env with ctx = ctx_z} e3 e9 e3_ty_expected ) ;
          lazy ( equiv env e5 e11 t1 ) ;
          lazy ( equiv env e6 e12 t1 );
          lazy ( equiv_whnf env e4 e10 (Syntax.Paths (t1, e5, e6), loc1) ) ;
        ]

    (* chk-eq-whnf-refl *)
    | Syntax.Refl(t, e1), Syntax.Refl(u, e2) ->
        joinSome
        [
          lazy ( equiv_ty env t u ) ;
          lazy ( equiv env e1 e2 t ) ;
        ]

    (* chk-eq-whnf-prod *)
    | Syntax.NameProd(alpha, beta, x, e1, e2), Syntax.NameProd(alpha', beta', _, e1', e2') ->
        joinSome
        [
          lazy ( if Universe.eq alpha alpha' then Some [] else None );
          lazy ( if Universe.eq beta beta' then Some [] else None );
          lazy ( equiv env e1 e1' (Syntax.Universe alpha, Position.nowhere) ) ;
          lazy ( let env' = {env with ctx = Context.add_var x (Syntax.El(alpha,e1), Position.nowhere) env.ctx } in
                 equiv env' e2 e2' (Syntax.Universe beta, Position.nowhere) ) ;
        ]

    (* chk-eq-whnf-universe *)
    | Syntax.NameUniverse alpha, Syntax.NameUniverse beta ->
        if (Universe.eq alpha beta) then Some [] else None

    (* chk-eq-whnf-unit *)              (** Subsumed by reflexivity check! *)
    (*| Syntax.NameUnit, Syntax.NameUnit -> true *)

    (* chk-eq-whnf-paths *)
    | Syntax.NamePaths(alpha, e1, e2, e3), Syntax.NamePaths(alpha', e1', e2', e3')
    (* chk-eq-whnf-id *)
    | Syntax.NameId(alpha, e1, e2, e3), Syntax.NameId(alpha', e1', e2', e3') ->
        joinSome
        [
          lazy ( if Universe.eq alpha alpha' then Some [] else None ) ;
          lazy ( equiv env e1 e1' (Syntax.Universe alpha, Position.nowhere) ) ;
          lazy ( equiv env e2 e2' (Syntax.El (alpha, e1), Position.nowhere) ) ;
          lazy ( equiv env e3 e3' (Syntax.El (alpha, e1), Position.nowhere) ) ;
        ]

    (* chk-eq-whnf-coerce *)
    | Syntax.Coerce(alpha, beta, e1), Syntax.Coerce(alpha', beta', e1') ->
        joinSome
        [
          lazy ( if Universe.eq alpha alpha' then Some [] else None ) ;
          lazy ( if Universe.eq beta beta' then Some [] else None ) ;
          lazy ( equiv env e1 e1' (Syntax.Universe alpha, Position.nowhere) ) ;
        ]

   | (Syntax.Var _ | Syntax.Equation _ | Syntax.Rewrite _ | Syntax.Ascribe _
      | Syntax.Lambda _ | Syntax.App _ | Syntax.Idpath _
      | Syntax.J _ | Syntax.Coerce _ | Syntax.NameUnit
      | Syntax.NameProd _ | Syntax.NameUniverse _ | Syntax.NamePaths _
      | Syntax.NameId _ | Syntax.UnitTerm | Syntax.Refl _ ), _ -> None

  end


let toplevel_handler =
  let k = "toplevel k" in
  {
    I.valH = None ;
    I.opH  = [ ("equiv", I.PWild, k,
                I.mkApp (I.mkVar k) (I.mkConst I.Unit)) ] ;
    I.finH = None ;
  }

let rec toprun env c =
  let c' = I.mkWithHandle (I.mkHandler toplevel_handler) c in
  run env c'

