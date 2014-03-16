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
  let add_parameters bnds  env = {env with ctx = Ctx.add_parameters bnds  env.ctx}

  let whnf env e = Norm.whnf env.ctx e
  let nf   env e = Norm.nf   env.ctx e

  let print_term env e ppf =
    begin
      (* We print Brazil syntax in color *)
      Format.fprintf ppf "\027[38;5;4m"; (* blue *)
      P.term env.ctx.Ctx.names e ppf;
      Format.fprintf ppf "\027[0m"       (* default colors *)
    end


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


  (******************************)
  (* {3 Metavariable Utilities} *)
  (******************************)

  (* If we create a fresh metavariable in the context a,b,c,d,
     then we declare the unknown M to be a function of its free variables, and
     actually build a term representing the application M a b c d. (More
     precisely, [a;b;c;d] is the mv_args list.)

     Thus, the unknown is a closed term, meaning that it is unaffected by shifts
     or substitutions. (The arguments a,b,c,d are affected normally, of course.)

     The trick is to do the de Bruijn bookkeeping properly when it's time to
     instantiate the variable. WLOG shifts and substitutions have turned the
     term into M c d b e, and suppose we've decided to instantiate

         M c d b e ===  d * e

     Intuitively we want M to be the function
         fun c d b e => d * e
     or, in de Bruijn notation,

         lam lam lam lam . Var(2) * Var(0)

     That is, the definition of the un-applied metavariable is like the
     instantiating definition, except that all variables are replaced by their
     distance from the end in the mv_args list. This translation of
     variable indices is constructed by [build_renaming] below.

     In the metavarapp data structure, the lambdas are implicit.


     All of this assumes that we're doing a pattern unification problem, which
     requires the arguments to the metavariable M are distinct variables, and
     that these collectively include all the free variables of the instantiating
     definition.
  *)



  (* Check that this is pattern unification, or transform it
     into such a problem.
   *)
  let pattern_check env args defn =
    let rec loop vars_seen = function
      | [] -> Some vars_seen
      | S.Var v :: rest  when not (S.VS.mem v vars_seen) ->
        loop (S.VS.add v vars_seen) rest
      | _ -> None
    in match loop S.VS.empty args with
    | None -> None
    | Some arg_var_set ->
        (* Arguments consist of distinct variables. Check they
           include all free variables in the definition. *)
        let free_in_defn = S.free_vars defn  in
        if (S.VS.is_empty (S.VS.diff free_in_defn arg_var_set)) then
           Some (defn, free_in_defn)
        else
           (* That didn't work. Lets try normalizing, in case some
              of the free variables disappear. *)
           let defn' = nf env defn in
           let free_in_defn' = S.free_vars defn'  in
           if (S.VS.is_empty (S.VS.diff free_in_defn' arg_var_set)) then
             Some (defn', free_in_defn')
           else
             None
             (*
             begin
               S.VS.iter (function i -> Format.printf "free var: %d  " i) first_try;
               Format.printf "@.";
               S.VS.iter (function i -> Format.printf "arg  var: %d  " i) arg_var_set;
               Format.printf "\nmetavariable= %s @."
                  (S.string_of_mva ~show_meta:true mva);

               Error.fatal ~pos:mva.S.mv_pos
                  "Cannot deduce term: defn has extra free variables"
             end
             *)

  (* Builds a mapping from each variable to its distance from the
     end of the list.

     Assumes that the arguments have already been verified as distinct
     variables.
   *)
  let arg_map args =
    let num_args = List.length args  in
    let rec loop index_in_list = function
      | []              -> S.VM.empty
      | S.Var v :: rest ->
        let how_far_from_list_end = num_args - (index_in_list+1)  in
        S.VM.add v how_far_from_list_end (loop (index_in_list+1) rest)
      | _               -> Error.impossible "arg_map: arg is not a Var"  in
    loop 0 args

  (* Figure out the required renumbering of variables from the
     instantiating definition to the metavariable's lambda body; see
     further explanation above.
  *)
  let build_renaming args defn_free_set =
    let amap = arg_map args in      (* Map arg vars to their position *)
    S.VS.fold (fun s m -> S.VM.add s (S.VM.find s amap) m) defn_free_set S.VM.empty


  (* Try to set an unset metavariable (application) to a term.
     Fails with an Error exception if this is not a pattern unification problem.
   *)
  let instantiate env mva defn =
    assert (not (S.mva_is_set mva));
    P.debug "instantiate: mva = %s, defn = %t@ = %s@."
      (S.string_of_mva ~show_meta:true mva) (print_term env defn)
      (S.string_of_term defn);
    (*Ctx.print env.ctx;*)

    match pattern_check env mva.S.mv_args defn with
    | None ->
      Error.fatal ~pos:mva.S.mv_pos "Cannot deduce term; not a pattern unification problem"
    | Some (defn, free_in_defn) ->
      begin
        (* XXX Occurs check? *)
        (* XXX Check that all variables and metavariables in definition
         * are "older than" the * metavariable *)

        let renaming_map : Common.debruijn S.VM.t =
          build_renaming mva.S.mv_args free_in_defn  in

        let renamed_defn =
          (* Traverse all variables in the definition *)
          S.rewrite_vars (fun bound_vars_in_term this_index ->
              if (this_index < bound_vars_in_term) then
                (* Leave bound variables alone *)
                S.Var this_index
              else
                (* Free variable. Subtract bound variable count to
                   see what it's called on the outside of the definition,
                   translate it to a top-level argument number, and then add
                   bound variable count back when we insert it into the middle
                   of the term.
                 *)
                 let renamed_index =
                   S.VM.find (this_index - bound_vars_in_term) renaming_map in
                 S.Var (bound_vars_in_term + renamed_index)) defn  in

        (* Store the metavariable's function definition without the implicit lambdas *)
        S.set_mva mva renamed_defn;

        (* P.debug "mva set to@ %t@." (print_term env (S.MetavarApp mva)); *)

        trivial_hr
      end



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
        let h1 = S.shift_to_depth (installdepth, h1) currentdepth  in
        let h2 = S.shift_to_depth (installdepth, h2) currentdepth  in

        P.debug "handle search expr = %t@. and h1 = %t@. and h2 = %t@."
          (print_term env expr) (print_term env h1) (print_term env h2) ;

        if (S.equal h1 expr && predicate h2) then
          let body    = D.shift_to_depth (installdepth, unshifted_body) currentdepth in
          let ty      = S.shift_to_depth (installdepth, unshifted_ty) currentdepth in
          let witness = check env body ty  in
          h2, singleton_hr witness
        else if (S.equal h2 expr && predicate h1) then
          let body    = D.shift_to_depth (installdepth, unshifted_body) currentdepth in
          let ty      = S.shift_to_depth (installdepth, unshifted_ty) currentdepth  in
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
  let reduct, hr = find_handler_reduction env expr
                  (function S.Pi _ -> true | _ -> false) in
  match reduct with
  | S.MetavarApp mva ->
      let dom_mva = S.derived_mva mva in
      let cod_mva = S.derived_mva mva in
      let arrow_type = S.make_arrow (S.MetavarApp dom_mva) (S.MetavarApp cod_mva)  in
      let hr_inst = instantiate env mva arrow_type in
      arrow_type, join_hr hr hr_inst
  | _ -> reduct, hr

  and as_sigma env expr =
  let reduct, hr = find_handler_reduction env expr
                  (function S.Sigma _ -> true | _ -> false)  in
  match reduct with
  | S.MetavarApp mva ->
      let dom_mva = S.derived_mva mva in
      let cod_mva = S.derived_mva mva in
      let star_type = S.make_arrow (S.MetavarApp dom_mva) (S.MetavarApp cod_mva)  in
      let hr_inst = instantiate env mva star_type in
      star_type, join_hr hr hr_inst
  | _ -> reduct, hr


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

  (*********************************)
  (* Checking if a type is fibered *)
  (*********************************)

  (** [type_of env e] returns the (annotated) type of the (annotated) expression
      e. This is very similar to the code in Brazil.Verify.infer, except that we
      assume the input is well-formed rather than double-checking that it is.

      Note: We currently assume that although the code uses as_u, as_pi, etc.,
      this will not result in any handlers being invoked. (We do check this,
      though.) If this assumption turns out to be wrong, we will have to rewrite
      these functions to return handler_results.
   *)
  and type_of env e =
    P.debug "type_of: e = %t@." (print_term env e);
    match e with
    | S.Var v -> lookup_classifier v env

    | S.Lambda(x, ty1, e) ->
        let env' = add_parameter x ty1 env in
        let ty2 = type_of env' e  in
        S.Pi(x, ty1, ty2)

    | S.Pi(x, ty1, ty2)
    | S.Sigma(x, ty1, ty2) ->
        let u1 = universe_of env ty1  in
        let env' = add_parameter x ty1 env  in
        let u2 = universe_of env' ty2  in
        S.U (S.universe_join u1 u2)

    | S.App(e1, e2) ->
        let x, ty1, ty2 = pi_type_of env e1  in
        S.beta ty2 e2

    | S.Pair(_, _, x, ty1, ty2) ->
        S.Sigma(x, ty1, ty2)

    | S.Proj(i, e) ->
        begin
          let x, ty1, ty2 = sigma_type_of env e  in
          match i with
          | 1 -> ty1
          | 2 -> S.beta ty2 (S.Proj(1,e))
          | _ -> Error.impossible "type_of found projection .%d" i
        end

    | S.Refl(o, e, ty) -> S.Eq(o, e, e, ty)

    | S.Eq(o, _, _, ty) ->
        begin
          match o, universe_of env ty with
          | S.Pr, S.Fib i    -> S.U (S.Fib i)
          | S.Pr, S.NonFib _ -> Error.impossible "type_of found = at non-fibered type"

          | S.Ju, S.NonFib i
          | S.Ju, S.Fib i    -> S.U (S.NonFib i)
        end

    | S.Ind_eq(_, _, (_,_,_,c), _, a, b, q) ->
        S.strengthen c [a;b;q]

    | S.U u -> S.U (S.universe_classifier u)

    | S.Base ty ->
        begin
          match ty with
          | S.TUnit -> S.U (S.Fib 0)
        end

    | S.Const const ->
        begin
          match const with
          | S.Unit -> S.Base S.TUnit
        end

    | S.Handle (e, _) ->
        begin
          (* Just in case we needed the handler to figure out the type *)
          try
            type_of env e
          with Error.Error (loc, sort, msg) ->
            let msg' = "in type_of that ignored handler...\n" ^ msg  in
            raise (Error.Error (loc, sort, msg'))
        end

    | S.MetavarApp mva -> mva.S.mv_ty

  and universe_of env ty =
    match as_u env (type_of env ty) with
    | S.U u, hr ->
        if (S.TermSet.is_empty hr) then
          u
        else
          Error.unimplemented "type_of: reduction to universe used a handler"
    | _ -> Error.fatal "type_of: Could not find a universe type for@ %t"
             (print_term env ty)

  and pi_type_of env exp =
    match as_pi env (type_of env exp) with
    | S.Pi (x, ty1, ty2), hr ->
        if (S.TermSet.is_empty hr) then
          x, ty1, ty2
        else
          Error.unimplemented "type_of: reduction to Pi used a handler"
    | _ -> Error.fatal "type_of: Could not find a Pi type for@ %t"
             (print_term env exp)

  and sigma_type_of env exp =
    match as_sigma env (type_of env exp) with
    | S.Sigma (x, ty1, ty2), hr ->
        if (S.TermSet.is_empty hr) then
          x, ty1, ty2
        else
          Error.unimplemented "type_of: reduction to Sigma used a handler"
    | _ -> Error.fatal "type_of: Could not find a Sigma type for@ %t"
             (print_term env exp)

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
    let answer_expr, answer_type =
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

    | D.Admit ->
      (* Temporary admits only allowed in checking positions, where we
         can infer their type
      *)
      Error.typing ~loc "Cannot infer this admit's type"

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

    | D.Refl(D.Ju, term1) ->
        begin
          (*
               G |- e : ty
               -----------------------------
               G |- refl e : (e == e @ ty)
           *)
          let e, ty = infer env term1 in
          let refl_exp = S.Refl(S.Ju, e, ty)  in
          let refl_ty  = S.Eq(S.Ju, e, e, ty)  in
          refl_exp, refl_ty
        end

    | D.Refl(D.Pr, term1) ->
        begin
          (*
               G |- e : ty    where ty is fibered
               ------------------------------------
               G |- idpath e : (e = e @ ty)
           *)
          let e, ty = infer env term1 in
          match universe_of env ty with
          | S.NonFib _ ->
              Error.typing ~loc "idpath found at non-fibered type %t"
                (print_term env ty)
          | _ ->
            let idpath_exp = S.Refl(S.Pr, e, ty)  in
            let idpath_ty  = S.Eq(S.Pr, e, e, ty) in
            idpath_exp, idpath_ty
        end

    | D.Ind((x,y,p,term1), (z,term2), term3) ->
        begin
          (*
               G |- t : Uf_i                               [Must be fibered.]
               G , x:t, y:t, z:(x = y @ t) |- c : Uf_j     [Must be fibered.]
               G , z:t |- w : c[x,y,p->z,z,idpath(z, t)]
               G |- a : t    G |- b : t    G |- q : (a = b @ t)
               -------------------------------------------------------------
               G |- Ind_eq(Pr, t, x.y.p.c, z.w, a, b, q) : c[x,y,p->a,b,q]


               G |- t : U_i
               G , x:t, y:t, z:(x == y @ t) |- c : U_j
               G , z:t |- w : c[x,y,p->z,z,refl(z, t)]
               G |- a : t    G |- b : t    G |- q : (a == b @ t)
               -------------------------------------------------------------
               G |- Ind_eq(Ju, t, x.y.p.c, z.w, a, b, q) : c[x,y,p->a,b,q]

               Note: term is written Ind(x.y.p.c, z.w, q) at the source level;
                     We infer a, b, and t from the type of q.

               By induction, if term3 is well-formed then so is its type.  Thus,
               if the path is a propositional equality, then it must be at a
               fibered type; we don't have to re-check it here.
          *)
          let q, o, a, b, t, hr = infer_eq env term3 in



          (* XXX: I think it would be slightly simpler to translate
             c and then do a weakening in the *middle* to get c' *)
          (* Term [term1] has indices relative to the context [env, x, y, p],
             so we create that environment for use during translation.
           *)
          let env_c =
            (* Unfortunately, add_parameters only works when there are
               no dependencies between the variables, so we have to
               do it in two stages. First we add x and y.
             *)
            let tmp_env =
                  add_parameters [ (x, t); (y, t) ] env in
            (* Then add p, with a type indexed relative to tmp_env
             *)
            let xvar = S.Var 1  in
            let yvar = S.Var 0  in
            let t'   = shift_to_env (env,t) tmp_env  in
            add_parameter p (S.Eq(o, xvar, yvar, t')) tmp_env  in

          (* Next, translate [term1] to annotated type [env, x, y, p |- c : U_j].
           *)
          let c, u_j = infer_ty env_c term1 in

          (* If we're working propositionally, check that c is fibered *)
          let _ = match o, u_j with
            | S.Pr, S.NonFib _ ->
                Error.typing ~loc "Eliminating prop equality %t@ in non-fibered family %t"
                  (print_term env q) (print_term env_c c)
            | _, _ -> ()  in

          (* [c] has indices relative to the context [env, x, y, p]
             but when working with [w] it would be more helpful to
             use the context [env, z, x, y, p] with z in position 3.
             We can adjust the indices to get a term [c'] by using weakening.
          *)
          let c' = S.weaken 3 c in

          (* [env_w] is the context [env, z:t].
           *)
          let env_w = add_parameter z t env in

          (* [term2] will be our [w] input. We expect that
                   [env, z:t |- w : c[x,y,p->z,z,refl z]],
             so we construct the type
                   [env, z:t |- c[x,y,p->z,z,refl z]].
             Fortunately, we have [env, z, x, y, p |- c'] so we can
             construct the desired substitution instance of [c]
             using strengthening.
           *)
          let w_ty_expected =
            (* We shift [env |- t] to get [env, z:t |- t']. *)
            let t' = shift_to_env (env,t) env_w  in
            (* In the context [env, z:t], variable z is represented by 0. *)
            let zvar = S.Var 0   in
            S.strengthen c' [zvar; zvar; S.Refl(o, zvar, t')]  in

          (* Finally, verify that [w] has the right type, and translated it
             into annotated form. *)
          let w = check env_w term2 w_ty_expected  in

          (* That's everything we needed to translate the induction expression
           *)
          let induction_exp =
            wrap_with_handlers (S.Ind_eq(o, t, (x,y,p,c), (z,w), a, b, q)) hr  in

          (* Now we need to compute the expression's type, e.g.,
                 c[x,y,p -> a,b,q].
             Since [env, x, y, p |- c], we can get this by strengthening.
           *)
          let induction_type = S.strengthen c [a;b;q]  in

          induction_exp, induction_type
        end

    | D.Operation (tag, terms) ->
      let operation = inferOp env loc tag terms None in
      inferHandler env loc operation

    | D.Handle (term, handlers) ->
      let env'= addHandlers env loc handlers in
      infer env' term

   in let _ = P.debug "infer returned@ %t with type %t@."
             (print_term env answer_expr) (print_term env answer_type)  in
     answer_expr, answer_type


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
    P.debug "Checked called with term = %s@ expecting type %t@."
      (D.string_of_term string_of_int term) (print_term env t);
    match term1 with
    | D.Wildcard ->
      let currentdepth = depth env in
      S.MetavarApp (S.fresh_mva currentdepth t loc S.MV_wildcard)
    | D.Admit ->
        let currentdepth = depth env in
        S.MetavarApp (S.fresh_mva currentdepth t loc S.MV_admit)
    | D.Handle (term, handlers) ->
      let env'= addHandlers env loc handlers in
      check env' term t

    | D.Lambda (x, None, term2) ->
      begin
        match as_pi env t with
        | S.Pi (_, t1, t2), hr_whnf ->
          let e2 = check (add_parameter x t1 env) term2 t2 in
          wrap_with_handlers (S.Lambda(x, t1, e2)) hr_whnf
        | _ -> Error.typing ~loc "Lambda cannot have type %t"
                 (print_term env t)
      end
    | D.Lambda (x, Some term1, term2) ->
      begin
        match as_pi env t with
        | S.Pi (_, t1, t2), hr_whnf ->
            begin
              let t1', _ = infer_ty env term1  in
              match Equiv.equal_at_some_universe env t1 t1' with
              | None -> Error.typing ~loc "@[<hov 4>Lambda should have domain@ %t@]"
                            (print_term env t1)
              | Some hr_equiv ->
                let e2 = check (add_parameter x t1 env) term2 t2 in
                let hr_all = join_hr hr_whnf hr_equiv  in
                wrap_with_handlers (S.Lambda(x, t1, e2)) hr_all
            end
        | _ -> Error.typing ~loc "@[<hov 4>Lambda cannot have type@ %t@]"
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
        | _ -> Error.typing ~loc "@[<hov 4>Pair cannot have type@ %t@]"
                 (print_term env t)
      end

    | D.Operation(D.Inhabit, []) ->
        let exp, _ = inferHandler env loc (Inhabit t)  in
        exp

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
              (print_term env e) (print_term env (whnf env t')) (print_term env
              (whnf env t))
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

  (* [infer_eq G term] does type synthesis on the given input [term],
     and checks that its type is (convertible to) an Eq .  If so, it returns the
     translated term and the 4 components of the Eq and any handlers used, all
     together as a 6-tuple.
  *)
  and infer_eq env ((_,loc) as term) =
    let exp, ty = infer env term in
    match (as_eq env ty) with
    | S.Eq(o, exp_lhs, exp_rhs, ty), hr -> exp, o, exp_lhs, exp_rhs, ty, hr
    | _ -> Error.typing ~loc "Expected an equality type, but@ %t@ has type@ %t"
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

end

