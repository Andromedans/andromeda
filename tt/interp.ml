module I = InputTT
module SM = InputTT.StringMap

let wrap = ref true

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
    | I.VTerm body, loc -> I.mkVTerm ~loc (Syntax.Lambda(x, t, Equal.type_of ctx body, body), loc)
    | I.VTuple es, loc  -> I.mkVTuple ~loc (List.map loop es)
    | I.VInj (i, e), loc -> I.mkVInj ~loc i (loop e)
    | I.VType u, loc -> I.mkVFakeTypeFamily 1 (Syntax.Prod(x, t, u), loc)
    | I.VFakeTypeFamily (n,u), loc -> I.mkVFakeTypeFamily (n+1) (Syntax.Prod(x, t, u), loc)
    | (_, loc) -> Error.runtime ~loc "Bad body to MkLam"  in
  loop

(** [witness_of_value ctx v] returns [b] if [v] is the Brazil term [b],
      and reports an error otherwise. The context is used just for error
      reporting (converting [v] to a string).
*)
let witness_of_value ctx0 = function
  | I.VTerm b, _  -> b
  | (_, loc) as w -> Error.runtime ~loc "Witness %s is not a term" (I.string_of_value ctx0 w)

(** If [v] is the Brazil term [b], [extend_context_with_witness ctx v] adds [b]
    to [ctx] as a generic hint. Otherwise, reports a runtime error.
  *)
let extend_context_with_witness ctx v =
  let w = witness_of_value ctx v  in
  let t = Equal.type_of ctx w  in
  let hint = Equal.as_hint ctx w t  in
  Context.add_equation hint ctx

(** If [l] is a list of Brazil terms, [extend_context_with_witnesses ctx l]
    adds them all to [ctx]. Otherwise, reports a runtime error.
  *)
let extend_context_with_witnesses =
  List.fold_left extend_context_with_witness


(** If [v] is the Brazil term [b'], [wrap_syntax_with_witness ctx b v]
    produces a brazil term wraps the Brazil term [b] with hint [b'].
    Otherwise, reports a runtime error.
  *)
let wrap_syntax_with_witness ctx b v =
  let w = witness_of_value ctx v in
  Syntax.Equation(w, Equal.type_of ctx w, b), Position.nowhere

(** [wrap_syntax_with_witnesses ctx b l] produces a Brazil term
    wrapping [b], but for a list [l] of Brazil term values.
 *)
let wrap_syntax_with_witnesses ctx =
  List.fold_left (wrap_syntax_with_witness ctx)


(** Representation of option types in TT *)

let none   = I.mkVInj 0 (I.mkVConst I.Unit)
let some x = I.mkVInj 1 x

let retSomeTuple ws = I.RVal (some (I.mkVTuple ws))
let retNone         = I.RVal none


(*******************************************)
(* Run-time parsing of literal Brazil code *)
(*******************************************)

(** Shifts the Lexing.position [p] rightwards [n] characters *)
let rightwards n p =
  { p with Lexing.pos_cnum = p.Lexing.pos_cnum + n }

(** Given a parsing function, the Position of the literal in the input, the
    number of characters within that literal where the Brazil syntax began, and
    the text itself, parse.

    Purposely not recursively defined with anything below, because
    we want to use it polymorphically (i.e., given a term-parser
    it returns a term, and given a type-parser it returns a type.
*)
let parse_literal parse_fn loc skipchars text =
     let lexbuf = Lexing.from_string text in
     let (startp, _) = Position.get_range loc  in
     lexbuf.Lexing.lex_curr_p <- (rightwards skipchars startp);
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

(** [insert_matched env (v,pat)] either inserts the TT values from [v] where there
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

  | I.VTerm (Syntax.NameId(_,_,b1,b2),loc), I.PJuEqual(pat1, pat2) ->
      List.fold_left (insert_matched ctx) env [I.mkVTerm ~loc b1,pat1; I.mkVTerm ~loc b2,pat2]


  | I.VType ((Syntax.Prod(x,t1,t2),loc) as t), I.PProd(pat1, pat2) ->
      insert_matched ctx (insert_matched ctx env (I.mkVType ~loc:(snd t1) t1, pat1))
             (I.mkVFakeTypeFamily ~loc 1 t, pat2)

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

(* [eval ctx env e] deterministically reduces TT expression [e] to a
   value. This largely involves looking up variables in the environment, running
   primitives, and building closures.
 *)
and eval ctx env (exp', loc) =
  match exp' with
  | I.Value v   -> v
  | I.Const a   -> I.VConst a, loc
  | I.Term b    -> I.VTerm b, loc
  | I.Type t    -> I.VType t, loc

  | I.Tuple es  -> I.VTuple (List.map (eval ctx env) es), loc

  | I.Inj(i,e)  -> I.VInj(i, eval ctx env e), loc

  | I.BrazilTermCode text ->
      (* Parse the string as a Brazil term *)
      eval_brazilterm ctx loc text

  | I.BrazilTypeCode text ->
      (* Parse the string as a Brazil type *)
      eval_braziltype ctx loc text

  | I.Prim(op, es) ->
      let vs = List.map (eval ctx env) es  in
      eval_prim ctx env loc op vs

  | I.Var x ->
      if SM.mem x env then
        (* Values in the environment are tagged with the depth of the
           context when they were inserted. We might have entered some
           lambdas or definitions since then, so any de Bruijn indices
           in that value would be wrong. Fix this, by shifting appropriately.
         *)
        let (value, insert_depth) = SM.find x env  in
        let current_depth = depth ctx in
        let delta = current_depth - insert_depth in
        (* The number of brazil variables only goes down when we leave the
           scope of a [lambda] computation, which any TT variables at that
           depth should already have gone out of scope. Thus, the shift
           should always be positive (referencing a TT variable created outside
           the [lambda] in the body of that [lambda]).
         *)
        assert (delta >= 0);
        I.shiftv 0 delta value
      else
        Error.runtime ~loc "Undefined variable %s" x

  | I.Fun (f, x, c) ->
     (* Create a closure *)
     I.VFun((fun env ctx self v ->
               let env' = insert_ttvar f self ctx env   in
               let env' = insert_ttvar x v    ctx env'  in
               run ctx env' c),
            env ), loc

  | I.Handler h -> I.VHandler (eval_handler loc h, env), loc


(** [eval_brazilterm ctx loc text] takes the string [text] and tries to parse it
    as a Brazil term relative to [ctx]. The position [loc] is used for
    error-reporting.
    *)
and eval_brazilterm ctx loc text =
        begin
          let skipchars = 1 in  (* skip the opening ` character *)
          let term = parse_literal Parser.topterm loc skipchars text  in
          let term = Debruijn.term (Context.names ctx) term in
          let term, _ty = Typing.syn_term ctx term  in
          I.mkVTerm ~loc term
        end

and eval_braziltype ctx loc text =
        begin
          let skipchars = 2 in (* skip the opening t` characters *)
          let term = parse_literal Parser.topty loc skipchars text  in
          let ty = Debruijn.ty (Context.names ctx) term in
          let ty = Typing.is_type ctx ty  in
          I.mkVType ~loc ty
        end


(** Apply the operation [op] to the given list of values [vs].
    Reports a runtime error if the arguments have the wrong
    number or type.
 *)
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
        let t = Equal.type_of ctx b  in
        I.mkVTerm (Equal.whnf ~use_rws:true ctx t b)

    | I.Whnf, [I.VType t, _] ->
        I.mkVType (Equal.whnf_ty ~use_rws:true ctx t)

    | I.GetCtx, [] ->
        (Context.print ~label:"getctx" ctx;
        I.mkVConst ~loc (I.Int (List.length (Context.names ctx))))

    | I.Explode, [v] -> eval_explode ctx env loc v

    | I.NameOf, [I.VType t, tloc] ->
        begin
          match Syntax.name_of t with
          | Some (e,u) ->
              I.mkVTuple [I.mkVTerm ~loc:tloc e;
                          I.mkVConst ~loc:tloc (I.String (Universe.to_string u))]   (* universe strings? *)
          | None -> Error.runtime ~loc "Type %s has no name" (I.string_of_ty ctx t)
        end

    | I.TypeOf, [I.VTerm b, bloc] ->
        I.mkVType ~loc:bloc (Equal.type_of ctx b)

    | _, _ -> Error.runtime ~loc "Primitive %s cannot handle argument list %s"
                                     (I.string_of_primop op) (I.string_of_value ctx (I.mkVTuple vs))

and eval_explode ctx _env loc value =

  let mkstr s = I.mkVConst (I.String s)  in

  let do_u u = I.mkVType (Syntax.Universe u, Position.nowhere)in

  let rec do_type ((ty',loc) as ty) =
    let components =
        match ty' with
        | Syntax.Universe u -> [mkstr "Universe"; mkstr (Universe.to_string u)]
        | Syntax.El(u,e) -> [mkstr "El"; do_u u; I.mkVTerm e]
        | Syntax.Unit -> [mkstr "Unit"]
        | Syntax.Prod(x1,t2,_) -> [mkstr "Prod"; I.mkVType t2; I.mkVFakeTypeFamily ~loc 1 ty]
        | Syntax.Paths(t1,e2,e3) -> [mkstr "Paths"; I.mkVType t1; I.mkVTerm e2; I.mkVTerm e3]
        | Syntax.Id(t1,e2,e3) -> [mkstr "Id"; I.mkVType t1; I.mkVTerm e2; I.mkVTerm e3]
    in
       I.mkVTuple ~loc components

   and do_term (term',_) =
    let components =
        match term' with
        | Syntax.Var i -> [mkstr "Var"; I.mkVConst (I.Int i)]
        | Syntax.Equation(e1,t2,e3) ->
            [mkstr "Equation"; I.mkVTerm e1; I.mkVType t2; I.mkVTerm e3]
        | Syntax.Rewrite(e1,t2,e3) ->
            [mkstr "Rewrite"; I.mkVTerm e1; I.mkVType t2; I.mkVTerm e3]
        | Syntax.Ascribe(e1,t2) ->
            [mkstr "Ascribe"; I.mkVTerm e1; I.mkVType t2]
        | Syntax.Lambda(x1,t2,t3,e4) ->
            [mkstr "Lambda"; mkstr x1; I.mkVType t2; I.mkVType t3; I.mkVTerm e4]
        | Syntax.App((_,t2,t3),e4,e5) ->
            [mkstr "App"; I.mkVType t2; I.mkVType t3; I.mkVTerm e4; I.mkVTerm e5]
        | Syntax.UnitTerm -> [mkstr "UnitTerm"]
        | Syntax.Idpath(t1,e2) -> [mkstr "Idpath"; I.mkVType t1; I.mkVTerm e2]
        | Syntax.J(t1,(x2,x3,x4,t5),(x6,e7),e8,e9,e10) ->
            let e7_as_lambda =
              (Syntax.Lambda(x6, t1,
                             Equal.type_of (Context.add_var x6 t1 ctx) e7,
                             e7), Position.nowhere)  in
            let t5_as_3_pis =
              (Syntax.Prod(x2, t1,
                 (Syntax.Prod(x3, Syntax.shift_ty 1 t1,
                    (Syntax.Prod(x3, (Syntax.Paths(Syntax.shift_ty 2 t1,
                                                (Syntax.Var 1, Position.nowhere),
                                                (Syntax.Var 0, Position.nowhere)), Position.nowhere),
                               t5), Position.nowhere)), Position.nowhere)), Position.nowhere)  in

            [mkstr "J"; I.mkVType t1;
             I.mkVFakeTypeFamily 3 t5_as_3_pis;
             I.mkVTerm e7_as_lambda;
             I.mkVTerm e8; I.mkVTerm e9; I.mkVTerm e10]
        | Syntax.Refl(t1,e2) -> [mkstr "Refl"; I.mkVType t1; I.mkVTerm e2]
        | Syntax.Coerce (u1,u2,e3) ->
            [mkstr "Coerce"; do_u u1; do_u u2; I.mkVTerm e3]
        | Syntax.NameUnit -> [mkstr "NameUnit"]
        | Syntax.NameProd(u1,u2,x3,e4,e5) ->
            [mkstr "NameProd"; do_u u1; do_u u2; mkstr x3; I.mkVTerm e4; I.mkVTerm e5]
        | Syntax.NameUniverse u ->
            [mkstr "NameUniverse"; do_u u]
        | Syntax.NamePaths(u1,e2,e3,e4) ->
            [mkstr "NamePaths"; do_u u1; I.mkVTerm e2; I.mkVTerm e3; I.mkVTerm e4]
        | Syntax.NameId(u1,e2,e3,e4) ->
            [mkstr "NameId"; do_u u1; I.mkVTerm e2; I.mkVTerm e3; I.mkVTerm e4]
    in
       I.mkVTuple ~loc components  in

    match fst value with
    | I.VType t -> do_type t
    | I.VTerm b -> do_term b
    | _ -> Error.runtime ~loc "Can't explode %s@." (I.string_of_value ctx value)

and eval_implode ctx env ((v',loc) as v) =
  match v' with
  | I.VTuple ((I.VConst (I.String s), _)::vs) ->
      begin
        match s,vs with
        | "Var", [I.VConst (I.Int i), iloc] ->
            if (i >= 0 && i < List.length (Context.names ctx)) then
              I.mkVTerm ~loc (Syntax.Var i, iloc)
            else
              Error.runtime ~loc "implode: invalid variable"

        | "NameUniverse", [I.VConst(I.String s), sloc] ->
          begin
            match Universe.of_string s with
            | Some u -> I.mkVTerm (Syntax.NameUniverse u, sloc)
            | None -> Error.runtime ~loc "'%s' is not a valid universe" s
          end

        | "Universe", [I.VConst(I.String s), sloc] ->
          begin
            match Universe.of_string s with
            | Some u -> I.mkVType (Syntax.Universe u, sloc)
            | None -> Error.runtime ~loc "'%s' is not a valid universe" s
          end

        | "El", _ ->
            Error.unimplemented "implode of El"

        | "Prod", [I.VType _t1, _; I.VFakeTypeFamily (1, ((Syntax.Prod(_,t1',t2'),_) as u)), _] ->
            (*if (Syntax.equal_ty t1 t1') then*)
               I.mkVType u
            (*else*)
              (*Error.runtime ~loc "implode: type family has wrong domain"*)

        | _ -> Error.runtime ~loc "Invalid list %s passed to implode"
                     (I.string_of_value ctx v)
      end
  | I.VTuple _ ->
      Error.runtime ~loc "Input to implode must start with a string"
  | _ -> Error.runtime ~loc "Input to implode must be a list"



(** [sequence k r] is a kind of bind operator for computations.
   It takes a computation that (already) evaluated to result $r$,
   and a continuation [k : I.value -> I.Result] that says what to do
   with that result once it has resolved to a value.


   If the result is an operation with continuation k', we want to handle that
   operation (including running the continuation k') and only then come back and
   do [k]. Equivalently, we want to handle the operation, and then do (result of
   [k'], followed by [k]).

   Now it may be that result r was running in an extended Brazil context, and
   that continuation [k] captures one or more Brazil variables (i.e., is the
   continuation of something like MkLam that locally introduces Brazil
   variables) result r is running in an extended Brazil context. If r produces a
   value, that's fine. But if it produces an operation, we want to report to the
   handler that the operation was in this extended context, so that the handler
   can similarly run in this extended context.

   For example, suppose the input is
      lambda x:`unit`, let z = op foo () in debruijn 0
      then the result r given to MkLam's sequence is basically
           ROp("foo", -, (), 'let z = [] in debruijn 0')
      where k is basically
           fun v -> abstract (...,x:unit) "x" 'unit' v
   The result of sequence thus floats to operation out, i.e.,
           ROp("foo", x:unit, (),
                'let v = (let z = [] in debruijn 0) in abstract (...,x:unit) "x" 'unit' v')

   Note that we expect the handler will invoke the continuation
   in the operation with its [ctx] parameter being the extended context.
   (handler's [ctx] ++ the [delta] in the operation).

 *)
and sequence ?(prependctx=Context.empty) ?(label="") k = function
  | I.RVal v -> k v
  | I.ROp(tag,delta,v,(k',eta)) ->
       Print.debug "sequence %s propagating operation %s" label tag;
       (*Context.print ~label:"prependctx" prependctx;*)
       let k'' env ctx u = sequence ~prependctx ~label k (k' env ctx u)  in
       I.ROp(tag, Context.append prependctx delta, v, (k'',eta) )

(** [eval_handler loc h] turns the syntactic handler [h] into a function
    from results to results, i.e., what to do with the result of the handled
    expression.
  *)
and eval_handler loc {I.valH; I.opH; I.finH} =
  (* In [hfun], parameter [env] stands for the TT environment at the point where
     the handler was *installed* (which by static scoping/closures should be the same
     as the environment where the handler is running).

     Parameter [ctx] stands for the context at the point where the handler
     is *installed*. In the [val] handler, this is the same as the context
     where the handler is running, but in the general case of other operations
     (originally invoked from inside lambda compuations), the handler will
     be running in an extended handler context ctx_h.
   *)
  let rec hfun env ctx = function
    | I.RVal v ->
        begin
          (* If the body is a value, then we run the "val" handler (outside
           * the scope of [h]). A missing val handler is equivalent to
           * "val x => val x", an identity transformation *)

          Print.debug "Handler %s produced value %s@." (Position.to_string loc) (I.string_of_value ctx v);
          match valH with
          | Some (xv,cv) ->
              run ctx (insert_ttvar xv v ctx env) cv
          | None ->
              I.RVal v
        end

    | I.ROp (opi, delta, v, (k,eta)) ->
        begin
          (* If the body of the handler is an operation, we need to handle it *)

          Print.debug "Handler produced operation %s@." opi;
          (*Context.print ~label:"ctx" ctx;*)
          (*Context.print ~label:"delta" delta;*)

          (* See comment for hfun *)
          let ctx_h = Context.append ctx delta  in

          (* If we find a match, the continuation of the handler is specified
             in the ROp, except we want to wrap that continuation with the
             handler.

             In theory, since we are reinstalling the handler, the environment
             and context may have grown. But, static scoping tells us that
             the handler should be reinvoked with the same environment
               i.e.,
                 h = handler
                      op foo _ k =>  x   + let x = 42 in k ()
                     end
                 should not cause the rewrapping of k by h to cause
                 the inner wrapping to capture the outer x with the
                 inner binding x=42.

             Since we don't permit shifting of continuations [for now, at
             least], the context ctx' at the point where k' is invoked should
             also be the same (extended) context ctx_h we had when the handler
             began running.

             More importantly, we want the val case of the handler to run
             in the same context where the handler was originally installed.
             If the rewrapped handler catches an exception, it will
             reconstruct the extended ctx_h from ctx + an appropriate delta.

             The tricky bit is that the continuation k returns a value
             well-formed in *ctx* (not ctx_h where the handler was running).
           *)
          let k' env' ctx' u =
            (* We expect ctx_h = ctx', but for now we're simplifying by
               checking only the names *)
            if (Context.names ctx_h <> Context.names ctx') then
              begin
                Context.print ~label:"ctx_h" ctx_h;
                Context.print ~label:"ctx'" ctx';
                failwith "assertion failure: these contexts should be identical"
              end
            else
              hfun env ctx
                 (sequence
                   (* Even though k resumes in an extended context ctx',
                      it will eventually bind all the extra variables, and return
                      a final result in context ctx. The handler thinks it's
                      always running in the extended context ctx_h, though, so we
                      fix this by weakening the result of k from context ctx to
                      ctx_h = ctx+delta, i.e., by shifting by delta.
                    *)
                   (fun v ->
                       I.RVal (I.shiftv 0 (List.length (Context.names delta)) v))
                   (k eta ctx' u))  in

          (* Continuation function [k'] as a TT run-time value *)
          let k'val = I.mkVCont ctx delta (k',env) in


          let rec loop = function
            | [] ->
                (Print.debug "No matching case found for body at position %s@." (Position.to_string loc);
                (*Context.print ~label:"ctx" ctx;*)
                (*Context.print ~label:"delta" delta;*)
                I.ROp(opi, delta, v, (k',env)))

            | (op, pat, kvar, c)::rest when op = opi ->
                begin
                  try
                    (* The handler's tag is correct, but don't report a true match
                     * unless that pattern-matching goes through as well.
                     *)
                    let env_h = insert_matched ctx_h env (v,pat) in

                    (* We found a match *)
                    Print.debug "Found matching case %s. Creating VCont with env = %s." op (string_of_env ctx env);
                    (*Context.print ~label:"ctx" ctx;*)
                    (*Context.print ~label:"delta" delta;*)

                    (* Add the continuation to the handler's environment env_h *)
                    let env_h = insert_ttvar kvar k'val ctx_h env_h  in

                    (* We want to run the handler body *including the
                      continuation of the original operation* (if the handler
                      actually invokes the continuation, that is).  As soon as
                      that resolves to a value [v'] (possibly because of outer
                      handlers), we want to check that the value makes sense.
                      Specifically, the handler was running in extended context
                      ctx_h = ctx ++ delta. We want the result to make sense in
                      context ctx, where this handler was installed.

                      If it does, there should be no references in the value [v']
                      to variables in delta, and hence we safely strengthen [v']
                      from ctx_h to ctx by shifting indices down by the length
                      of delta.
                    *)
                    sequence ~prependctx:delta
                     (fun v' ->
                          Print.debug "Eval_handler on %s computed value %s@." opi (I.string_of_value ctx_h v');
                          (*Context.print ~label:"ctx" ctx;*)
                          (*Context.print ~label:"delta" delta;*)
                          let unshift_amount = - (List.length (Context.names delta)) in
                          Print.debug "unshift_amount = %d@." unshift_amount;
                          if vok ctx v' then
                            I.RVal (I.shiftv 0 unshift_amount v')
                          else
                            Error.runtime ~loc "Handler returned value with too
                            many variables")
                     (run ctx_h env_h c)
                  with
                    NoPatternMatch ->
                      (* tag matched but pattern didn't; try the remaining handlers *)
                      loop rest
                end
            | _ :: rest ->
                (* tag didn't match; try the remaining handlers. *)
                loop rest in
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



(*************************)
(* Running a Computation *)
(*************************)


and run ctx env  (comp, loc) =
  Print.debug "run: %s\n%s" (I.string_of_computation ctx (comp,loc))
  (string_of_env ctx env);
  (*Context.print ~label:"run ctx" ctx;*)

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
            (*Context.print ~label:"ctx" ctx;*)
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
              let t1 = Equal.type_of ctx b1  in
              match Equal.whnf_ty ~use_rws:true ctx t1 with
              | Syntax.Prod(x,t,u), _ ->
                  begin
                    let t2 = Equal.type_of ctx b2 in
                    sequence ~label:"App(Term)"
                      (function
                        | I.VInj(1, (I.VTuple ws, _)), _ ->
                            let ctx' = extend_context_with_witnesses ctx ws in
                            if Equal.equal_ty ctx' t t2 then
                              I.RVal (I.mkVTerm (wrap_syntax_with_witnesses ctx
                                                    (Syntax.App((x,t,u),b1,b2), loc) ws))
                            else
                              Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
                        | v' ->  Error.runtime ~loc "Bad mkApp. Why is@ %t@ == %t ? (%s)"
                                 (print_ty ctx t) (print_ty ctx t2) (I.string_of_value ctx v')
                      )
                      (equiv_ty ctx env t t2)
                  end
              | _ -> Error.runtime ~loc "Can't prove operator in application is a product"
            end

        | I.VFakeTypeFamily (n,t1), I.VTerm b2 ->
            begin
              match t1 with
              | Syntax.Prod(x,t,u), _ ->
                  begin
                    let t2 = Equal.type_of ctx b2 in
                    sequence ~label:"App(TypeFamily)"
                      (function
                        | I.VInj(1, (I.VTuple ws, _)), _ ->
                            let ctx' = extend_context_with_witnesses ctx ws in
                            if Equal.equal_ty ctx' t t2 then
                              let t1' = Syntax.beta_ty u
                                          (wrap_syntax_with_witnesses ctx b2 ws) in
                              if (n = 1) then
                                I.RVal (I.mkVType t1')
                              else
                                I.RVal (I.mkVFakeTypeFamily (n-1) t1')
                            else
                              Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
                        | v' ->  Error.runtime ~loc "Bad mkApp. Why is@ %t@ == %t ? (%s)"
                                 (print_ty ctx t) (print_ty ctx t2) (I.string_of_value ctx v')
                      )
                      (equiv_ty ctx env t t2)
                  end
              | _ -> Error.runtime ~loc "Can't prove operator is a type family"
            end

        | _, _ -> Error.runtime ~loc "Bad application"
      end

  | I.Let(pat,c1,c2) ->
      begin
        let r = run ctx env c1  in
        sequence ~label:"Let"
                 (fun v ->
                    let env' =
                      (try insert_matched ctx env (v,pat)
                       with
                        | NoPatternMatch ->
                           Error.runtime ~loc "let pattern-match failed") in
                    run ctx env' c2) r
      end

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
                     let t = Equal.type_of ctx b  in
                     match Equal.as_universe ctx t with
                     | Some alpha -> Syntax.El(alpha, b), snd e2
                     | None -> Error.runtime ~loc
                                "Bad type annotation in lambda.@ Why does %t belong to a universe?"
                                (print_term ctx b)
                   end
              | v2 -> Error.runtime ~loc "Bad type annotation in lambda; found %s"
                           (I.string_of_value ~brief:false ctx v2)   in

          let _ = Print.debug "MkLam: domain = %t@." (print_ty ctx domain)  in

          let ctx' = Context.add_var x1 domain ctx  in
          let r3 = run ctx' env c3  in

          (*let domain' = Syntax.weaken_ty 0 domain  in*)  (* Why does t.tt want me to abstract here? *)

          (* r3 is the result of running the body. Once that has resolved to
             value, we want to abstract it as "lambda x1:domain, ..."

             But r3 was running in the extended context ctx'...

          *)
          sequence ~prependctx:(Context.add_var x1 domain Context.empty) ~label:"MkLam"
            (fun v3 ->
                 (Print.debug "At the point where we actually abstract the lambda@.";
                  (*Context.print ~label:"ctx" ctx;*)
                  Print.debug "and the abstracting type domain = %t" (print_ty ctx domain);
                  I.RVal (abstract ctx' x1 domain v3))) r3
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
                let u = Equal.type_of ctx b  in
                sequence ~label:"Ascribe"
                  (function
                    | I.VInj(1, (I.VTuple ws, _)), _ ->
                        let ctx' = extend_context_with_witnesses ctx ws in
                        if Equal.equal_ty ctx' u t then
                          I.RVal
                               (I.mkVTerm (wrap_syntax_with_witnesses ctx
                                             (Syntax.Ascribe(b,t), Position.nowhere) ws ))
                        else
                          Error.runtime ~loc "Witnesses weren't enough to prove equivalence"
                    | _ ->
                        Error.runtime ~loc "Brazil could not produce witnesses for the ascription"
                  )
                 (equiv_ty ctx env u t)
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
    begin
      Print.debug "equiv_ty: %t == %t" (print_ty ctx t) (print_ty ctx u);
      let userCmd =
        I.mkApp (I.mkVar "equiv_ty")
                (I.mkTuple [ I.mkType t ; I.mkType u ])  in
      run ctx env userCmd
    end


let toplevel_handler =
  let k = "toplevel k" in
  let continue_with_unit = I.mkApp (I.mkVar k) (I.mkConst I.Unit)  in
  let doPrint ctx ttenv v =
    (Format.printf "%s@." (I.string_of_value ~brief:true ctx v);
     Print.debug "finished printing, I hope";
     I.RVal (I.mkVConst I.Unit))  in
  {
    I.valH = None ;
    I.opH  = [ ("equiv_ty", I.PWild, k, continue_with_unit);
               ("print", I.PVar "x", k, I.mkLet I.PWild (I.mkRunML doPrint (I.mkVar "x"))
                                          continue_with_unit) ;
             ] ;

    I.finH = None ;
  }

let rec toprun ctx env c =
  let c' =
    if !wrap then
      I.mkWithHandle (I.mkHandler toplevel_handler) c
    else
      c in
  run ctx env c'

