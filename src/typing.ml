(**************************************************************)
(** {1 Type inference for the TT (i.e., user-level) language.} *)
(**************************************************************)

(**
   We must define equivalence-checking and type checking mutually recursively.
   Obviously, type checking requires equality checking (e.g., when we have
   inferred a term has type T but the context expect a value of type U) but in
   TT, equivalence checking also requires type checking. This occurs because
   equivalence checking may require "running" TT handlers (e.g., inhabitation of
   equivalence types), and "running" in the context of TT really means type
   checking (and returning the annotated term).

   It is likely that we will soon need to add extra well-formedness checks to
   equivalence checking, because extending the equational theory may break some
   normally admissible rules (such as injectivity of Pi's, see Harper &
   Pfenning, TOCL 2005) that mean the usual equivalence algorithm can assume
   inputs are well-formed, without requiring extra well-formedness checks before
   recursive calls.

*)


(*******************)
(** {2 Signatures} *)
(*******************)

(**
   The inference module will expose:
    {ol {- Everything the equivalence algorithm (functor) needs;}
        {- The type it uses when tracking handler usage (because this
            seems necessary to get the recursive-module definition
            type check);}
        {- Additional functions called by the top-level code in [tt.ml].}}
*)
module type INFER_SIG = sig

  include Equivalence.EQUIV_ARG
    with type handled_result = BrazilSyntax.TermSet.t

  type iterm = Common.debruijn Input.term

  val empty_env : env
  val get_ctx   : env -> BrazilContext.Ctx.context

  val infer : env -> iterm -> term * term
  val inferParam               : ?verbose:bool -> env -> Common.variable list
    -> iterm -> env
  val inferDefinition          : ?verbose:bool -> env -> Common.variable
    -> iterm -> env
  val inferAnnotatedDefinition : ?verbose:bool -> env -> Common.variable
    -> iterm -> iterm -> env

  val addHandlers: env -> Common.position
    -> Common.debruijn Input.handler
    -> env



end


(************)
(* {2 Code} *)
(************)

(**
   We use the same equivalence algorithm (and even the same code/functor) for
   the TT and Brazil levels, so we can predict when checking TT inputs exactly
   what handlers will be needed during Brazil verification.

   We can't factor out the public signature of Equiv and give it a name, because
   it refers to the Infer module being defined in the recursion. Fortunately,
   the signature is fairly short.
*)
module rec Equiv : sig

  (**
   * Assuming the given two terms belong to *some* common universe (and in
   * particular, are both well-formed in the given environment), return
   *  - [None   ]   if they are not provably equal
   *  - [Some hr]   if they are, where hr encapsulates the information about
   *                     handlers used to prove the equivalence
  *)

  val equal_at_some_universe : Infer.env -> Infer.term -> Infer.term
    -> Infer.handled_result option

end = Equivalence.Make(Infer)

(**
   The main job of type inference is to verify well-formedness of TT inputs. For
   well-formed inputs, we produce a fully annotated translation (the "Brazil"
   syntax) with very simplified handlers, and the (fully annotated) type.
*)
and Infer : INFER_SIG = struct

  (*******************************************************)
  (** {3 Convenience abbreviations of modules and types} *)
  (*******************************************************)

  module D   = Input                 (** TT [input] syntax *)
  module S   = BrazilSyntax          (** Fully-annotated Brazil [output] syntax *)
  module Ctx = BrazilContext.Ctx     (** Fully-annotated typing contexts *)
  module P   = BrazilPrint           (** Printing functions for Brazil syntax *)

  type iterm = Common.debruijn Input.term  (** Input terms *)
  type term  = BrazilSyntax.term           (** Output terms *)

  (***************************)
  (** {3 Typing Enviroments} *)
  (***************************)

  (** The type [env] represents the typing environment, which includes
        - a mapping from variables to its type or type + definition
  *)
  type env = {
    ctx        : Ctx.context;
    handlers   : (depth * operation * Common.debruijn D.handler_body) list;
    equiv_entry_depth : depth option;
  }

  (**
     We call the length of the context at some point in time its [depth].

     If you have a term that was well-formed in a context of depth [d1], and
     later the context has been extended to reach depth [d2 > d1], then to make
     the term well-formed in this new context, we [shift] the term by [d2 - d1].
  *)
  and depth = int

  and operation =
    | Inhabit of S.term                   (** inhabit a type *)
    | Coerce  of S.term * S.term          (** t1 >-> t2 *)

  let empty_env = { ctx               = Ctx.empty_context;
                    handlers          = [];
                    equiv_entry_depth = None;
                  }

  let get_ctx { ctx } = ctx

  let depth env = Ctx.depth env.ctx

  let enter_equiv env =
    { env with equiv_entry_depth = Some (depth env) }

  let get_equiv_entry env =
    match env.equiv_entry_depth with
    | None        -> Error.fatal "No equiv_entry_depth value was set!"
    | Some depth  -> depth

  (** [shiftOperation] extends the [S.shift] function to Brazil operation values
  *)
  let shiftOperation ?(cut=0) delta = function
    | Inhabit term      -> Inhabit (S.shift ~cut delta term)
    | Coerce (ty1, ty2) -> Coerce  (S.shift ~cut delta ty1, S.shift ~cut delta ty2)

  (* {4 Wrap functions expecting raw Ctx info to accept env values} *)

  let lookup            v env = Ctx.lookup v env.ctx
  let lookup_classifier v env = Ctx.lookup_classifier v env.ctx
  let shift_to_env (env1, exp) env2 = Ctx.shift_to_ctx (env1.ctx, exp) env2.ctx

  let add_parameter  x t   env = {env with ctx = Ctx.add_parameter  x t   env.ctx}
  let add_definition x t e env = {env with ctx = Ctx.add_definition x t e env.ctx}

  let whnf env e = Norm.whnf env.ctx e
  let nf   env e = Norm.nf   env.ctx e

  let print_term env e = P.term env.ctx.Ctx.names e


  (***********************)
  (* {3 Handler Results} *)
  (***********************)

  (* The equivalence algorithm and our various generalizations of whnf reduction
     need to tell us which instances of handlers they needed. We define a suitable
     semilattice of such information.
  *)

  type handled_result = S.TermSet.t              (** A set of annotated terms *)
  let join_hr hr1 hr2 = S.TermSet.union hr1 hr2
  let trivial_hr      = S.TermSet.empty
  let singleton_hr    = S.TermSet.singleton

  (** When we get the results back from equivalence, we want to record
      in the annotated term what was needed. This convenience function
      adds the wrapper, unless no handlers were required.
  *)
  let wrap_with_handlers expr witness_set =
    match (S.TermSet.elements witness_set) with
    | []        -> expr
    | witnesses -> S.Handle(expr, witnesses)


  (*****************************************)
  (* {3 Searching for applicable handlers} *)
  (*****************************************)


  let rec find_handler_reduction env expr predicate =
    let currentdepth = depth env  in
    let rec loop = function

      | [] ->
        P.debug "find_handler_reduction defaulting to whnf@.";
        whnf env expr, trivial_hr

      | (installdepth, Inhabit(S.Eq(S.Ju,h1,h2,_) as unshifted_ty), unshifted_body)::rest ->
        (* XXX: is it safe to ignore the classifier??? *)
        let d = currentdepth - installdepth in
        let h1 = S.shift d h1  in
        let h2 = S.shift d h2  in

        P.debug "handle search expr = %t@. and h1 = %t@. and h2 = %t@."
          (print_term env expr) (print_term env h1) (print_term env h2) ;

        if (S.equal h1 expr && predicate h2) then
          let body    = D.shift d unshifted_body in
          let ty      = S.shift d unshifted_ty in
          let witness = check env body ty  in
          h2, singleton_hr witness
        else if (S.equal h2 expr && predicate h1) then
          let body    = D.shift d unshifted_body in
          let ty      = S.shift d unshifted_ty in
          let witness = check env body ty  in
          h1, singleton_hr witness
        else
          loop rest
      | _ :: rest -> loop rest
    in
    loop env.handlers

  (**
       Look for a handler that equates
  *)
  and as_pi env expr =
    find_handler_reduction env expr (function S.Pi _ -> true | _ -> false)

  and as_sigma env expr =
    find_handler_reduction env expr (function S.Sigma _ -> true | _ -> false)

  and as_u env expr =
    find_handler_reduction env expr (function S.U _ -> true | _ -> false)

  and as_eq env expr =
    find_handler_reduction env expr (function S.Eq _ -> true | _ -> false)


  and as_whnf_for_eta env expr =
    find_handler_reduction env expr
      (function
        | S.Pi _
        | S.Sigma _
        | S.Eq(S.Ju, _, _, _)
        | S.Base S.TUnit      -> true   (* The types where eta matters *)
        | _                   -> false
      )

  (**********************)
  (* {3 Type Inference} *)
  (**********************)


  (** [infer env e] infers the type of expression [e] in context [env].
      It returns a pair containing an internal (annotated) form of the
      expression, and its internal (annotated) type.
  *)
  and infer env ((term', loc) as term) =
    P.debug "Infer called with term = %s@." (D.string_of_term string_of_int term);
    (*Ctx.print env.ctx;*)
    (*let answer_expr, answer_type =*)
    match term' with

    | D.Var v      ->
      begin
          (*
               G |- v : G(v)
           *)
        S.Var v, lookup_classifier v env
      end

    | D.Universe u ->
      begin
          (*
               G |- U_i : U_{i+1}
           *)
        S.U u, S.U (S.universe_classifier u)
      end

    | D.Pi (x, term1, term2) ->
      begin
          (*
               G |- ty1 : U_i     G, x:U_i |- ty2 : U_j
               ----------------------------------------
               G |- Pi x:ty1. ty2  : U_i \/ U_j
           *)
        let ty1, u_i = infer_ty env term1 in
        let ty2, u_j = infer_ty (add_parameter x ty1 env) term2  in
        S.Pi(x, ty1, ty2), S.U (S.universe_join u_i u_j)
      end

    | D.Sigma (x, term1, term2) ->
      begin
          (*
               G |- ty1 : U_i     G, x:U_i |- ty2 : U_j
               ----------------------------------------
               G |- Sigma x:ty1. ty2  : U_i \/ U_j
           *)
        let ty1, u_i = infer_ty env term1 in
        let ty2, u_j = infer_ty (add_parameter x ty1 env) term2  in
        S.Sigma(x, ty1, ty2), S.U (S.universe_join u_i u_j)
      end

    | D.Lambda (x, Some term1, term2) ->
      begin
          (*
               G |- ty1 : U_i     G, x:ty1 |- e2 : t2
               ----------------------------------------
               G |- fun (x:t1) => e2  :  Pi x:ty1. ty2
           *)
        let ty1, _  = infer_ty env                       term1 in
        let e2, ty2 = infer    (add_parameter x ty1 env) term2 in
        S.Lambda (x, ty1, e2), S.Pi(x, ty1, ty2)
      end

    | D.Lambda (x, None, _) ->
      (* In a synthesis position, lambda requires a type annotation
      *)
      Error.typing ~loc "Cannot infer the argument's type"

    | D.Wildcard ->
      (* Wildcards are only allowed in checking positions, where we
         can infer their type
      *)
      Error.typing ~loc "Cannot infer this wildcard's type"

    | D.App (term1, term2) ->
        begin
          (*
               G |- e1 : Pi x:ty1. ty2     G |- e2 : ty1
               -----------------------------------------
               G |- e1 e2  :  ty2[x->e2]
           *)
          let e1, x, ty1, ty2, hr = infer_pi env term1  in
          let e2      = check env term2 ty1  in
          let app_exp = wrap_with_handlers (S.App(e1, e2)) hr  in
          let app_ty  = S.beta ty2 e2  in
          app_exp, app_ty
        end

    | D.Pair (term1, term2) ->
        begin
          (*
               G |- e1 : ty1    G |- e2 : ty2
               -----------------------------------------------------
               G |- (e1, e2)  :  ty1 * ty2  [ === Sigma _:ty1. ty2 ]

             For type synthesis, we always infer a non-dependent product type.  If
             you want a dependent sigma type, the pair must be used in an
             analysis context (e.g., a pair inside a type ascription or as a
             function argument.)
           *)
          let e1, ty1 = infer env term1  in
          let e2, ty2 = infer env term2  in


          (* ty2 is well-formed in env, but the second component of the sigma
             needs to be well-formed in  (env, _:ty1).

             Equivalently, ty2' = shift 1 ty2
           *)
          let ty2' = shift_to_env (env, ty2) (add_parameter "_" ty1 env)  in
          let pair_ty = S.Sigma("_", ty1, ty2')  in

          (* We annotate all pairs with their component types, so that
             the verifier can figure out whether we intended a dependent Sigma
             type or not.
           *)
          let pair_exp = S.Pair(e1, e2, "_", ty1, ty2')  in

          pair_exp, pair_ty
        end

    | D.Proj (("1"|"fst"), term1) ->
        begin
          (*
                G |- e : Sigma x:ty1. ty2
                -------------------------
                G |- fst e : ty1
          *)
          let e, _, ty1, _, hr = infer_sigma env term1  in
          let proj_exp = wrap_with_handlers (S.Proj(1, e)) hr  in
          let proj_ty = ty1  in
          proj_exp, proj_ty
        end

    | D.Proj (("2"|"snd"), term1) ->
        begin
          (*
                G |- e : Sigma x:ty1. ty2
                -------------------------
                G |- snd e : ty2[x->fst e]
          *)
          let e, _, _, ty2, hr = infer_sigma env term1  in
          let proj_exp = wrap_with_handlers (S.Proj(2, e)) hr  in
          let proj_ty = S.beta ty2 (S.Proj(1, e))  in
          proj_exp, proj_ty
        end

    | D.Proj (s1, _) ->
        Error.typing ~loc "Unrecognized projection %s" s1

    | D.Ascribe (term1, term2) ->
        begin
          (*
               G |- e : ty
               ------------------
               G |- (e : ty) : ty

               The typing rule doesn't look very interesting, but operationally
               this is where we switch from synthesis to checking, which lets
               us do things like give a pair a dependent-sigma type.
          *)
          let ty, _ = infer_ty env term2  in
          let e     = check env term1 ty  in
          e, ty
        end

    | D.Equiv(o, term1, term2, term3) ->
        begin
          (*
               G |- ty: Uf_i   where Uf_i is fibered
               G |- e1 : ty
               G |- e2 : ty
               -------------------------------------
               G |- (e1 = e2 @ ty) : Uf_i


               G |- ty : U_i   where U_i is unfibered
               G |- e1 : ty
               G |- e2 : ty
               --------------------------------------
               G |- (e1 == e2 @ ty) : U_i
           *)

          let ty, u_i = infer_ty env term3 in

          (* Confirm that the universe is fibered or that this
             is a judgmental equality type (in which case the type is unfibered
             or could be promoted to unfibered by universe inclusion).

             Compute this potentially promoted universe type.
           *)
          let equality_ty = match o, u_i with
            | D.Pr, D.Fib    i
            | D.Ju, D.NonFib i -> S.U u_i

            | D.Ju, D.Fib    i -> S.U (S.NonFib i)

            | D.Pr, D.NonFib _ ->
                Error.typing ~loc "@[<hov>Propositional equality over non-fibered type@ %t@]"
                  (print_term env ty)  in

          let e1 = check env term1 ty  in
          let e2 = check env term2 ty  in
          let equality_exp = S.Eq(o, e1, e2, ty)  in

          equality_exp, equality_ty
        end

    | D.Refl(o, term2) ->
        begin
          (*
               G |- e : ty    where ty is fibered
               ------------------------------------
               G |- idpath e : (e = e @ ty)

               G |- e : ty
               -----------------------------
               G |- refl e : (e == e @ ty)
           *)

          (* XXX: Need to check that ty is fibered if
                  this is a propositional equality!
           *)
          let e2, t2 = infer env term2 in
          S.Refl(o, e2, t2), S.Eq(o, e2, e2, t2)
        end

    | D.Ind((x,y,p,term1), (z,term2), term3) ->
      begin
        let q, ty3 = infer env term3 in
        match as_eq env ty3 with
        | S.Eq(o, a, b, t), hr ->
          begin
            let illegal_variable_name = "eventual.z" in
            let env_c' = add_parameter p (S.Eq(o, S.Var 1, S.Var 0, S.shift 3 t))
                (add_parameter y (S.shift 2 t)
                   (add_parameter x (S.shift 1 t)
                      (add_parameter illegal_variable_name t env)))  in
            (* We've inserted eventual.z into position 3 of the context
               where desugaring wasn't expecting it. So we need to shift all
               references to variables 3 and up by 1,but leave variables 0, 1, and 2
               (i.e., p, y, and x) alone. *)
            let c' = match infer_ty env_c' (D.shift ~cut:3 1 term1) with
              | c', S.NonFib _ when o = D.Pr ->
                Error.typing ~loc "Eliminating prop equality %t@ in non-fibered family %t"
                  (print_term env q) (print_term env_c' c')
              | c', _ -> c'  in
            let env_w = add_parameter z t env in
            let w_ty_expected = S.beta (S.beta (S.beta c' (S.Refl(o, S.Var 3, S.shift 3 t)))
                                          (S.Var 1))
                (S.Var 0)  in
            let w = check env_w term2 w_ty_expected  in

            (* c was translated in a context with the extra eventual.z
               variable, so we need to undo that by shifting variables
               numbered 3 and above down by one. (We know that c does not refer to
               eventual.z, so there's no chance of a reference to eventual.z
               turning into a reference to variable 2, i.e., x. *)
            let c = S.shift ~cut:3 (-1) c'  in
            let expression =
              wrap_with_handlers (S.Ind_eq(o, t, (x,y,p,c), (z,w), a, b, q)) hr  in

            (* Now we need to compute the expression's type. In the book
               this is [c a b q], except that the variables are in the context
               in the order [x, y, p], so we need to eliminate [p] first.
               We also need to adjust the arguments, because they are all
               well-formed in the context [env]. Note that [c] is in the
               context without the extra [eventual.z] variable. *)
            let expression_type =
              (S.beta (S.beta (S.beta c
                                 (S.shift 2 q))
                         (S.shift 1 b))
                 a)  in

            expression, expression_type
          end
        | _ -> Error.typing ~loc "Not a witness for equality or equivalence:@ %t" (print_term env q)
      end

    | D.Operation (tag, terms) ->
      let operation = inferOp env loc tag terms None in
      inferHandler env loc operation

    | D.Handle (term, handlers) ->
      let env'= addHandlers env loc handlers in
      let _ = P.debug "About to infer the body of handle-expression"  in
      infer env' term
  (* in let _ = P.debug "infer returned@ %t with type %t@."
             (print_term env answer_expr) (print_term env answer_type)  in
     answer_expr, answer_type *)


  and inferOp env loc tag terms handlerBodyOpt =
    match tag, terms, handlerBodyOpt with
    | D.Inhabit, [term], _ ->
      let ty, _ = infer_ty env term  in
      Inhabit ty

    | D.Inhabit, [], Some handlerBody ->
      (* Hack for Brazil compatibility *)
      let _, ty = infer env handlerBody  in
      Inhabit (whnf env ty)

    | D.Inhabit, _, _ -> Error.typing ~loc "Wrong number of arguments to INHABIT"

    | D.Coerce, [term1; term2], _ ->
      let t1, _ = infer_ty env term1  in
      let t2, _ = infer_ty env term2  in
      Coerce(t1, t2)

    | D.Coerce, _, _ -> Error.typing ~loc "Wrong number of arguments to COERCE"


  and addHandlers env loc handlers =
    let installdepth = depth env  in
    let rec loop = function
      | [] -> env
      | (tag, terms, handlerBody) :: rest ->
        (* When we add patterns, we won't be able to use inferOp any more... *)
        let operation = inferOp env loc tag terms (Some handlerBody) in
        let env' = { env with handlers = ((installdepth, operation, handlerBody) :: env.handlers) } in
        addHandlers env' loc rest  in
    loop handlers

  (* It might be safer for check to return hr separately, and wrap the context
   * of the check instead. But a handler here is compatible with
   * the current Brazil verification algorithm. *)
  and check env ((term1, loc) as term) t =
    match term1 with
    | D.Wildcard ->
      let currentdepth = depth env in
      S.MetavarApp (S.fresh_mva currentdepth t loc)
    | D.Lambda (x, None, term2) ->
      begin
        match as_pi env t with
        | S.Pi (_, t1, t2), hr_whnf ->
          let e2 = check (add_parameter x t1 env) term2 t2 in
          wrap_with_handlers (S.Lambda(x, t1, e2)) hr_whnf
        | _ -> Error.typing ~loc "Lambda cannot have type %t"
                 (print_term env t)
      end
    | D.Pair (term1, term2) ->
      begin
        match as_sigma env t with
        | S.Sigma(x, t1, t2), hr_whnf ->
          let e1 = check env term1 t1  in
          let t2' = S.beta t2 e1  in
          let e2 = check env term2 t2'  in
          wrap_with_handlers (S.Pair(e1, e2, x, t1, t2)) hr_whnf
        | _ -> Error.typing ~loc "Pair cannot have type %t"
                 (print_term env t)
      end
    | _ ->
      let e, t' = infer env term in
      match t with
      | S.U u ->
        begin
          match as_u env t' with
          | S.U u', hr_whnf when S.universe_le u' u ->
            wrap_with_handlers e hr_whnf
          | _ ->
            Error.typing ~loc "expression %t@ has type %t@\nBut should have type %t"
              (print_term env e) (print_term env t') (print_term env t)
        end
      | _ ->
        begin
          let _ = P.debug "Switching from synthesis to checking."  in
          let _ = P.debug "Expression %t@ has type %t@ and we expected type %t@."
              (print_term env e) (print_term env t') (print_term env t)  in
          let env = enter_equiv env  in
          match (Equiv.equal_at_some_universe env t' t ) with
          | None ->
            Error.typing ~loc "expression %t@ has type %t@\nbut should have type %t"
              (print_term env e) (print_term env t') (print_term env t)
          | Some witness_set -> wrap_with_handlers e witness_set
        end

  and infer_ty env ((_,loc) as term) =
    let t, k = infer env term in
    let _ = P.debug "infer_ty given %t\ni.e., %s@."
        (print_term env t) (D.string_of_term string_of_int term)  in
    match as_u env k with
    | S.U u, hr_whnf -> wrap_with_handlers t hr_whnf, u
    | _ -> Error.typing ~loc "Not a type: %t" (print_term env t)

  (* [infer_pi G term] does type synthesis on the given input [term],
     and checks that its type is (convertible to) a Pi.  If so, it returns the
     translated term and the 3 components of the Pi and any handlers used, all
     together as a 5-tuple.
  *)
  and infer_pi env ((_,loc) as term) =
    let exp, ty = infer env term in
    match (as_pi env ty) with
    | S.Pi(x, t1, t2), hr -> exp, x, t1, t2, hr
    | _ -> Error.typing ~loc "Expected a Pi type, but@ %t@ has type@ %t"
             (print_term env exp) (print_term env ty)

  (* [infer_sigma G term] does type synthesis on the given input [term],
     and checks that its type is (convertible to) a Sigma.  If so, it returns the
     translated term and the 3 components of the Sigma and any handlers used, all
     together as a 5-tuple.
  *)
  and infer_sigma env ((_,loc) as term) =
    let exp, ty = infer env term in
    match (as_sigma env ty) with
    | S.Sigma(x, ty1, ty2), hr -> exp, x, ty1, ty2, hr
    | _ -> Error.typing ~loc "Expected a Sigma type, but@ %t@ has type@ %t"
             (print_term env exp) (print_term env ty)

  and handled env e1 e2 _ =
    let currentdepth = depth env  in
    let _ = P.debug "Entering 'handled' with@ e1 = %t and@ e2 = %t"
        (print_term env e1) (print_term env e2)   in
    let rec loop = function
      | [] ->
        P.debug "handle search failed@.";
        None
      | (installdepth, op1, comp) :: rest ->
        begin
          (* XXX: is it safe to ignore the classifier??? *)
          let d = currentdepth - installdepth in
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
               let shift_out = ( get_equiv_entry env )   - currentdepth  in
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
    let currentdepth = depth env  in
    let rec loop = function
      | [] -> Error.typing ~loc "Unhandled operation"
      | (installdepth, op1, comp1)::rest ->
        let d = currentdepth - installdepth in
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


  (******************************)
  (* {3 Metavariable Utilities} *)
  (******************************)

  let patternCheck args =
    let rec loop vars_seen = function
      | [] -> Some vars_seen
      | S.Var v :: rest  when not (S.VS.mem v vars_seen) ->
        loop (S.VS.add v vars_seen) rest
      | _ -> None
    in
    loop S.VS.empty args

  let arg_map args =
    let num_args = List.length args  in
    let rec loop i = function
      | []              -> S.VM.empty
      | S.Var v :: rest ->
        let how_far_from_list_end = num_args - (i+1)  in
        S.VM.add v how_far_from_list_end (loop (i+1) rest)
      | _               -> Error.impossible "arg_map: arg is not a Var"  in
    loop 0 args

  let build_renaming args defn_free_set =
    let amap = arg_map args in      (* Map arg vars to their position *)
    S.VS.fold (fun s m -> S.VM.add s (S.VM.find s amap) m) defn_free_set S.VM.empty

  let instantiate env mva defn =
    assert (not (S.mva_is_set mva));
    (*Format.printf "instantiate: mva = %s, defn = %t@."*)
    (*(S.string_of_mva ~show_meta:true mva) (X.print_term env defn);*)
    match patternCheck mva.S.mv_args with
    | None ->
      Error.fatal ~pos:mva.S.mv_pos "Cannot deduce term; not a pattern unification problem"
    | Some arg_var_set ->
      begin
        (* Again, to stay in the pattern fragment we need the definition's
         * free variables to be included in our argument variables.
         * We try to minimize these free variables by normalizing,
         * which might expand away definitions, etc. *)
        let defn, free_in_defn =
          (let first_try = S.free_vars defn  in
           if (S.VS.is_empty (S.VS.diff first_try arg_var_set)) then
             defn, first_try
           else
             let defn' = nf env defn in
             let second_try = S.free_vars defn'  in
             if (S.VS.is_empty (S.VS.diff second_try arg_var_set)) then
               defn', second_try
             else
               Error.fatal ~pos:mva.S.mv_pos "Cannot deduce term: defn has extra free variables")  in

        (* XXX Occurs check? *)
        (* XXX Check that all variables and metavariables in definition
         * are "older than" the * metavariable *)

        let renaming_map : Common.debruijn S.VM.t =
          build_renaming mva.S.mv_args free_in_defn  in

        let renamed_defn =
          S.rewrite_vars (fun c m ->
              if (m < c) then
                S.Var m
              else
                S.Var (S.VM.find (m-c) renaming_map)) defn  in

        S.set_mva mva renamed_defn;

        Some trivial_hr
      end

end

