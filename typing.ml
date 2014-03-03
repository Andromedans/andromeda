(** Type inference. *)

module rec Equiv : sig
                     (* Assuming the given two terms belong to *some*
                      * common universe (and in particular, are both
                      * well-formed in the given environment), return
                      *    None      if they are not provably equal
                      *    Some hr   if they are, where hr encapsulates
                      *                the information about handlers
                      *                used to prove the equivalence
                      *)
                     val equal_at_some_universe :
                            Infer.env -> Infer.term -> Infer.term
                                      -> Infer.handled_result option
                   end =
  Equivalence.Make(Infer)

and Infer : sig
  type term = BrazilSyntax.term
  type env

  val empty_env         : env
  val get_ctx           : env -> BrazilContext.Ctx.context
  val add_parameter     : Common.variable -> term -> env -> env
  val lookup_classifier : Common.debruijn -> env -> term
  val whnf              : env -> term -> term
  val print_term        : env -> term -> Format.formatter -> unit

  type handled_result = BrazilSyntax.TermSet.t
  val trivial_hr : handled_result
  val join_hr    : handled_result -> handled_result -> handled_result

  val handled : env -> term -> term -> term option -> handled_result option
  val as_whnf_for_eta : env -> term -> term
  val as_pi   : env -> term -> term
  val as_sigma : env -> term -> term
  (* val as_u     : env -> term -> term  *)


  type iterm = Common.debruijn Input.term

  val infer : env -> iterm -> term * term
  val inferParam : ?verbose:bool -> env -> Common.variable list -> iterm -> env
  val inferDefinition : ?verbose:bool -> env -> Common.variable -> iterm -> env
  val inferAnnotatedDefinition : ?verbose:bool -> env -> Common.variable
                                   -> iterm -> iterm -> env

  val addHandlers: env -> Common.position
                       -> Common.debruijn Input.handler
                       -> env
end = struct

  module D   = Input
  module S   = BrazilSyntax
  module Ctx = BrazilContext.Ctx
  module P   = BrazilPrint

  type operation =
    | Inhabit of S.term                   (* inhabit a type *)
    | Coerce  of S.term * S.term          (* t1 >-> t2 *)

  let  shiftOperation ?(cut=0) d = function
    | Inhabit term -> Inhabit (S.shift ~cut d term)
    | Coerce (ty1, ty2) -> Coerce (S.shift ~cut d ty1, S.shift ~cut d ty2)

  type level = int (* The length of the context at some point in time. *)

  type env = {
    ctx : Ctx.context;
    handlers : (level * operation * Common.debruijn D.handler_body) list;
    equiv_entry_level : level option;
  }


  let empty_env = { ctx = Ctx.empty_context;
                    handlers = [];
                    equiv_entry_level = None;
                  }

  let get_ctx { ctx } = ctx

  let currentLevel env = List.length env.ctx.Ctx.names

  let add_parameter x t env =
    {env with ctx = Ctx.add_parameter x t env.ctx}
  let add_definition x t e env =
    {env with ctx = Ctx.add_definition x t e env.ctx}

  let enter_equiv env =
    { env with equiv_entry_level = Some (currentLevel env) }

  let get_equiv_entry env =
    match env.equiv_entry_level with
    | None        -> Error.fatal "No equiv_entry_level value was set!"
    | Some level  -> level

  let lookup v env = Ctx.lookup v env.ctx
  let lookup_classifier v env = Ctx.lookup_classifier v env.ctx
  let whnf env e = BrazilNorm.whnf env.ctx e
  let print_term env e = P.term env.ctx.Ctx.names e

  type iterm = Common.debruijn Input.term
  type term = BrazilSyntax.term

  (*******************)
  (* Handler Results *)
  (*******************)

  (* In order for the equivalence algorithm to tell us which instances of
   * handlers it needed, we must specify *)

  type handled_result = BrazilSyntax.TermSet.t
  let join_hr hr1 hr2 = BrazilSyntax.TermSet.union hr1 hr2
  let trivial_hr = BrazilSyntax.TermSet.empty


  (* XXX FIXME
   * THESE ARE SILENTLY USING HANDLERS WITHOUT TELLING EQUIVALENCE!!! *)

  let find_handler_reduction env k p =
    let level = currentLevel env  in
    let rec loop = function
      | [] ->
        P.debug "find_handler_reduction defaulting to whnf@.";
        whnf env k
      | (installLevel, Inhabit(S.Eq(S.Ju,h1,h2,_)), comp)::rest ->
        (* XXX: is it safe to ignore the classifier??? *)
        let d = level - installLevel in
        let h1 = S.shift d h1  in
        let h2 = S.shift d h2  in
        P.debug "handle search k = %t@. and h1 = %t@. and h2 = %t@."
          (print_term env k)
          (print_term env h1) (print_term env h2) ;
        if (S.equal h1 k && p h2) then
          h2
        else if (S.equal h2 k && p h1) then
          h1
        else
          loop rest
      | _ :: rest -> loop rest
    in
    loop env.handlers

  let as_pi env k =
    find_handler_reduction env k (function S.Pi _ -> true | _ -> false)

  let as_sigma env k =
    find_handler_reduction env k (function S.Sigma _ -> true | _ -> false)

  let as_u env k =
    find_handler_reduction env k (function S.U _ -> true | _ -> false)

  let as_whnf_for_eta env k =
    find_handler_reduction env k
      (function
        | S.Pi _ | S.Sigma _ | S.U _
        | S.Eq(S.Ju, _, _, _)
        | S.Base S.TUnit                -> true
        | _                             -> false)


  (** [infer env e] infers the type of expression [e] in context [env].
      It returns a pair containing an internal (annotated) form of the
      expression, and its internal (annotated) type. *)

  let rec infer env (term, loc) =
    match term with

    | D.Var v -> S.Var v, lookup_classifier v env

    | D.Universe u -> S.U u, S.U (S.universe_classifier u)


    | D.Pi (x, term1, term2) ->
      begin
        let t1, u1 = infer_ty env term1 in
        let t2, u2 = infer_ty (add_parameter x t1 env) term2  in
        S.Pi(x, t1, t2), S.U (S.universe_join u1 u2)
      end

    | D.Sigma (x, term1, term2) ->
      begin
        let t1, u1 = infer_ty env term1 in
        let t2, u2 = infer_ty (add_parameter x t1 env) term2  in
        S.Sigma(x, t1, t2), S.U (S.universe_join u1 u2)
      end

    | D.Lambda (x, Some term1, term2) ->
      begin
        let t1, _  = infer_ty env term1 in
        let t2, u2 = infer (add_parameter x t1 env) term2 in
        S.Lambda (x, t1, t2), S.Pi(x, t1, u2)
      end

    | D.Lambda (x, None, _) -> Error.typing ~loc "Cannot infer the argument type"


    | D.App (term1, term2) ->
      begin
        let e1, t1 = infer env term1  in
        let _, t11, t12 =
          match (as_pi env t1) with
          | S.Pi(x, t1, t2) -> x, t1, t2
          | _ -> Error.typing ~loc "Not a function: %t" (print_term env t1)  in
        let e2 = check env term2 t11  in
        let appTy = S.beta t12 e2  in
        S.App(e1, e2), appTy
      end

    | D.Pair (term1, term2) ->
      begin
        (* For inference, we always infer a non-dependent product type.
         * If you want a dependent sigma type, the pair must be used
         * in an analysis context (e.g., a pair inside a type
         * ascription)
         *)
        let e1, t1 = infer env term1  in
        let e2, t2 = infer env term2  in
        let ty = S.Sigma("_", t1, S.shift 1 t2)  in
        S.Pair(e1,e2), ty
      end

    | D.Proj (("1"|"fst"), term2) ->
      begin
        let e2, t2 = infer env term2  in
        (* XXX FIXME. Need to wrap a handler around the projection *)
        match as_sigma env t2 with
        | S.Sigma(_, t21, _) ->  S.Proj(1, e2), t21
        | _ -> Error.typing ~loc "Projecting from %t with type %t"
                 (print_term env e2) (print_term env t2)
      end

    | D.Proj (("2"|"snd"), term2) ->
      begin
        let e2, t2 = infer env term2  in
        (* XXX FIXME. Need to wrap a handler around the projection *)
        match as_sigma env t2 with
        | S.Sigma(_, _, t22) -> S.Proj(2, e2), S.beta t22 (S.Proj(1, e2))
        | _ -> Error.typing ~loc "Projecting from %t with type %t"
                 (print_term env e2) (print_term env t2)
      end

    | D.Proj (s1, _) -> Error.typing ~loc "Unrecognized projection %s" s1

    | D.Ascribe (term1, term2) ->
      begin
        let t2, _ = infer_ty env term2  in
        let e1    = check env term1 t2  in
        e1, t2
      end


    | D.Operation (tag, terms) ->
      let operation = inferOp env loc tag terms None in
      inferHandler env loc operation

    | D.Handle (term, handlers) ->
      let env'= addHandlers env loc handlers in
      infer env' term

    | D.Equiv(o, term1, term2, term3) ->
      begin
        let ty3, u3 = infer_ty env term3 in
        let e1 = check env term1 ty3  in
        let e2 = check env term2 ty3  in

        (* Make sure that judgmental equivalences are not marked fibered *)
        let ubase = match o with D.Pr -> S.Fib 0 | D.Ju -> S.Type 0 in
        let u = S.universe_join ubase u3  in

        S.Eq (o, e1, e2, ty3), S.U u
      end

    | D.Refl(o, term2) ->
        begin
          let e2, t2 = infer env term2 in
          S.Refl(o, e2, t2), S.Eq(o, e2, e2, t2)
        end

  and inferOp env loc tag terms handlerBodyOpt =
    match tag, terms, handlerBodyOpt with
    | D.Inhabit, [term], _ ->
      let ty, _ = infer_ty env term  in
      Inhabit ty

    | D.Inhabit, [], Some handlerBody ->
      (* Hack for Brazil compatibility *)
      let _, ty = infer env handlerBody  in
      Inhabit ty

    | D.Inhabit, _, _ -> Error.typing ~loc "Wrong number of arguments to INHABIT"

    | D.Coerce, [term1; term2], _ ->
      let t1, _ = infer_ty env term1  in
      let t2, _ = infer_ty env term2  in
      Coerce(t1, t2)

    | D.Coerce, _, _ -> Error.typing ~loc "Wrong number of arguments to COERCE"


  and addHandlers env loc handlers =
    let installLevel = currentLevel env  in
    let rec loop = function
      | [] -> env
      | (tag, terms, handlerBody) :: rest ->
        (* When we add patterns, we won't be able to use inferOp any more... *)
        let operation = inferOp env loc tag terms (Some handlerBody) in
        let env' = { env with handlers = ((installLevel, operation, handlerBody) :: env.handlers) } in
        addHandlers env' loc rest  in
    loop handlers

  and check env ((term1, loc) as term) t =
    match term1 with
    | D.Lambda (x, None, term2) ->
      begin
        match as_pi env t with
        | S.Pi (_, t1, t2) ->
          let e2 = check (add_parameter x t1 env) term2 t2 in
          S.Lambda(x, t1, e2)
        | _ -> Error.typing ~loc "Lambda cannot have type %t"
                 (print_term env t)
      end
    | D.Pair (term1, term2) ->
      begin
        match as_sigma env t with
        | S.Sigma(x, t1, t2) ->
          let e1 = check env term1 t1  in
          let t2' = S.beta t2 e1  in
          let e2 = check env term2 t2'  in
          S.Pair(e1, e2)
        | _ -> Error.typing ~loc "Pair cannot have type %t"
                 (print_term env t)
      end
    | _ ->
      let e, t' = infer env term in
      match t with
      | S.U u ->
        begin
          match as_u env t' with
          | S.U u' when S.universe_le u' u -> e
          | _ ->
            Error.typing ~loc "expression %t@ has type %t@\nBut should have type %t"
              (print_term env e) (print_term env t') (print_term env t)
        end
      | _ ->
        begin
          let env = enter_equiv env  in
          match (Equiv.equal_at_some_universe env t' t ) with
          | None ->
            Error.typing ~loc "expression %t@ has type %t@\nbut should have type %t"
              (print_term env e) (print_term env t') (print_term env t)
          | Some witness_set ->
            begin
              match (S.TermSet.elements witness_set) with
              | [] -> e
              | witnesses -> S.Handle(e, witnesses)
            end
        end

  and infer_ty env ((_,loc) as term) =
    let t, k = infer env term in
    match as_u env k with
    | S.U u -> t, u
    | _ -> Error.typing ~loc "Not a type: %t" (print_term env t)

  and handled env e1 e2 _ =
    let level = currentLevel env  in
    let rec loop = function
      | [] ->
        P.debug "handle search failed@.";
        None
      | (installLevel, op1, comp) :: rest ->
        begin
          (* XXX: is it safe to ignore the classifier??? *)
          let d = level - installLevel in
          let op1 = shiftOperation d op1  in
          let comp = Input.shift d comp  in
          match op1 with
          | Inhabit( S.Eq( S.Ju, h1, h2, _) as ty) ->
            P.debug "handle search e1 = %t@. and e2 = %t@. and h1 = %t@. and h2 = %t@."
              (print_term env e1) (print_term env e2)
              (print_term env h1) (print_term env h2) ;
            if ( (S.equal e1 h1 && S.equal e2 h2) ||
                 (S.equal e1 h2 && S.equal e2 h1) ) then
              (P.debug "handler search succeeded. Witness %s@. with expected type %t@."
                 (Input.string_of_term string_of_int comp) (print_term env ty);
               let witness = check env comp ty  in
               (* The problem is that we might be in the middle of some
                * complex equivalence that has extended the context with
                * additional variables, relative to where we were when
                * type inference invoked the equivalence checker. The
                * witness makes sense here, but due to de Bruijn notation,
                * has to be "unshifted" in order to make sense in the
                * original context. We therefore store the witness
                * in the form that makes sense in the original [type inference]
                * context. *)
               let shift_out = ( get_equiv_entry env )   - level  in
               let shifted_witness = S.shift shift_out witness  in
               P.debug "That witness %s will turn out to be %t@.Shifting it by %d to get %s"
                 (Input.string_of_term string_of_int comp)
                 (print_term env witness)
                 shift_out
                 (S.string_of_term shifted_witness);
               Some (S.TermSet.singleton shifted_witness))
            else
              loop rest
          | _ -> loop rest
        end
    in
    loop env.handlers


  (* Find the first matching handler, and return the typechecked right-hand-side
  *)
  and inferHandler env loc op =
    let level = currentLevel env  in
    let rec loop = function
      | [] -> Error.typing ~loc "Unhandled operation"
      | (installLevel, op1, comp1)::rest ->
        let d = level - installLevel in
        let op1 = shiftOperation d op1  in
        if (op = op1) then
          begin
            (* comp1' is the right-hand-size of the handler,
             * shifted so that its free variables are correct
             * in the context where the operation occurred.
            *)
            let comp1' = D.shift d comp1  in

            match op with
            | Inhabit ty ->
              check env comp1' ty, ty
            | Coerce (ty1, ty2) ->
              let ty = S.Pi("_", ty1, S.shift 1 ty2)  in
              check env comp1' ty, ty
          end
        else
          loop rest
    in
    loop (env.handlers)



  let inferParam ?(verbose=false) env names ((_,loc) as term) =
    let ty, _ = infer_ty env term  in
    let env, _ =
      List.fold_left
        (fun (env, t) name ->
           (*if List.mem x ctx.names then Error.typing ~loc "%s already exists" x ;*)
           if verbose then Format.printf "Term %s is assumed.@." name ;
           (add_parameter name t env, S.shift 1 t))
        (env, ty) names   in
    env

  let inferDefinition ?(verbose=false) env name ((_,loc) as termDef) =
    let expr, ty = infer env termDef in
    begin
      if verbose then Format.printf "Term %s is defined.@." name;
      add_definition name ty expr env;
    end

  let inferAnnotatedDefinition ?(verbose=false) env name ((_,loc) as term) termDef =
    let ty, _ = infer_ty env term in
    let expr = check env termDef ty  in
    add_definition name ty expr env

end

