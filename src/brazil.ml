

(* Note: It would be nicer to define Ctx here instead of in its own
 *   "BrazilContext" file/module, but Verify needs to refer to Norm
 *   and Norm needs to reference BrazilContext, so Norm would
 *   have to be defined in this file too, or maybe in Equivalence.
 *   And I'm not prepared to do that yet.
 *)


(***********************************)
(** Equivalence Testing for Brazil *)
(***********************************)

module rec Equiv : sig
                     val equal_at_some_universe : Verify.env ->
                            Verify.term -> Verify.term
                            -> Verify.handled_result option
                   end =
    Equivalence.Make(Verify)

(****************************)
(* Type Checking for Brazil *)
(****************************)

and Verify : sig
  type term = BrazilSyntax.term

  type env
  val empty_env         : env
  val get_ctx           : env -> BrazilContext.Ctx.context
  val add_parameter     : Common.variable -> term -> env -> env
  val lookup_classifier : Common.debruijn -> env -> term
  val whnf              : env -> term -> term
  val nf                : env -> term -> term
  val print_term        : env -> term -> Format.formatter -> unit

  type handled_result = unit
  val trivial_hr : handled_result
  val join_hr    : handled_result -> handled_result -> handled_result

  val handled : env -> term -> term -> term option -> handled_result option
  val as_whnf_for_eta : env -> term -> term * handled_result
  val as_pi   : env -> term -> term * handled_result
  val as_sigma : env -> term -> term * handled_result
  (* val as_u     : env -> term -> term  *)

  val instantiate : env -> BrazilSyntax.metavarapp
                        -> term
                        -> handled_result option

  type iterm = BrazilSyntax.term

  val infer : env -> iterm -> term
  val verifyContext : BrazilContext.Ctx.context -> unit
 end = struct


(** Type inference. *)

module Ctx = BrazilContext.Ctx
module P = BrazilPrint
module S = BrazilSyntax



type env = {
  ctx : Ctx.context;
  handlers : (int * S.term * S.term) list;  (* int is the install-depth *)
}

let empty_env = { ctx = Ctx.empty_context;
                  handlers = [];
                 }
let get_ctx { ctx } = ctx

let depth env = Ctx.depth env.ctx

let add_parameter x t env =
  {env with ctx = Ctx.add_parameter x t env.ctx}
let add_definition x t e env =
  {env with ctx = Ctx.add_definition x t e env.ctx}

let lookup v env = Ctx.lookup v env.ctx
let lookup_classifier v env = Ctx.lookup_classifier v env.ctx
let whnf env e = Norm.whnf env.ctx e
let nf env e = Norm.nf env.ctx e
let print_term env e = P.term env.ctx.Ctx.names e

type iterm = BrazilSyntax.term

type term = BrazilSyntax.term
type handled_result = unit
let join_hr _ _ = ()
let trivial_hr = ()




let unshift_handler env (installdepth, h1, h2) =
  let d = depth env - installdepth in
  S.shift d h1, S.shift d h2

(* We check handlers in both directions, so that the user is not required
 * to worry about symmetry, i.e., which direction to specify the equivalence *)

(* XXX : is it OK to ignore the classifier? *)
let handled env e1 e2 _ =
  let rec loop = function
    | [] ->
      P.debug "handle search failed@.";
      None
    | handler :: rest ->
        let h1, h2 = unshift_handler env handler  in
        P.debug "handle search e1 = %t@. and e2 = %t@. and h1 = %t@. and h2 = %t@."
          (print_term env e1) (print_term env e2)
          (print_term env h1) (print_term env h2) ;
        if ( (S.equal e1 h1 && S.equal e2 h2) ||
             (S.equal e1 h2 && S.equal e2 h1) ) then
               (P.debug "handler search succeeded.@.";
                Some ())
        else
          loop rest
  in
    loop (env.handlers)


let find_handler_reduction env k p =
  let rec loop = function
    | [] -> whnf env k, ()
    | handler::rest ->
        let h1, h2 = unshift_handler env handler  in
        if (S.equal h1 k && p h2) then
          h2, ()
        else if (S.equal h2 k && p h1) then
          h1, ()
        else
          loop rest  in
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

let rec infer env term =
  match term with

    | S.Var v -> lookup_classifier v env

    | S.U u -> S.U (S.universe_classifier u)

    | S.Pi    (x, term1, term2)
    | S.Sigma (x, term1, term2) ->
      begin
        let u1 = infer_ty env term1 in
        let env' = add_parameter x term1 env in
        let u2 = infer_ty env' term2  in
        S.U (S.universe_join u1 u2)
      end

    | S.App (term1, term2) ->
        begin
          let ty1 = infer env term1  in
          match (as_pi env ty1) with
          | S.Pi (_, ty11, ty12), () ->
            let _     = check env term2 ty11  in
            let appTy = S.beta ty12 term2  in
            appTy
          | _ -> Error.verify "Not a function: %t" (print_term env term1)
        end

    | S.Pair (term1, term2) ->
        begin
          let ty1 = infer env term1  in
          let ty2 = infer env term2  in
          S.Sigma("_", ty1, S.shift 1 ty2)
        end

    | S.Proj (1, term2) ->
        begin
          let ty2 = infer env term2  in
          match as_sigma env ty2 with
          | S.Sigma(_, ty21, _), () ->  ty21
          | _ -> Error.verify "Projecting from %t with type %t"
                    (print_term env term2) (print_term env ty2)
        end

    | S.Proj (2, term2) ->
        begin
          let ty2 = infer env term2  in
          match as_sigma env ty2 with
          | S.Sigma(_, _, ty22), () ->  S.beta ty22 (S.Proj(1, term2))
          | _ -> Error.verify "Projecting from %t with type %t"
                    (print_term env term2) (print_term env ty2)
        end

    | S.Proj (index, _) -> Error.verify "Unrecognized projection %d" index

    | S.Lambda (x, term1, term2) ->
        begin
          let _   = infer_ty env term1 in
          let ty2 = infer (add_parameter x term1 env) term2 in
          S.Pi(x, term1, ty2)
        end

    | S.Handle (term, handlers) ->
        let env'= addHandlers env handlers in
        infer env' term

    | S.Eq(o, term1, term2, term3) ->
        begin
          let u3 = infer_ty env term3 in
          let _ = match o, u3 with
                | S.Ju, _ -> ()
                | _,    S.Fib _ -> ()
                | _,    _ -> Error.verify
                               "@[<hov>Propositional equality over non-fibered type@ %t@]"
                               (print_term env term3)  in

          let _  = check env term1 term3  in
          let _  = check env term2 term3  in

          (* Make sure that judgmental equivalences are not marked fibered *)
          let ubase = match o with S.Pr -> S.Fib 0 | S.Ju -> S.NonFib 0 in
          let u = S.universe_join ubase u3  in

          S.U u
        end

    | S.Refl(o, term1, term2) ->
        let _ = infer_ty env term2  in
        let _ = check env term1 term2  in
        S.Eq(o, term1, term1, term2)


    | S.Base S.TUnit  -> S.U (S.Fib 0)

    | S.Const S.Unit -> S.Base S.TUnit

    | S.Ind_eq(o, t, (x,y,p,c), (z,w), a, b, q) ->
        begin
            (*let _ = P.debug "!! Original term = %s" (S.string_of_term term) in*)
            (*let _ = P.debug "!! Original term = %t" (print_term env term) in*)
            (*let _ = Ctx.print env.ctx in*)
            let _     = infer_ty env t  in
            let _     = check env a t   in
            let _     = check env b t   in
            let pathtype = S.Eq(o, a, b, t) in
            let _     = check env q pathtype  in

            let illegal_variable_name = "eventual.z" in
            let env_c' = add_parameter p (S.Eq(o, S.Var 1, S.Var 0, S.shift 3 t))
                          (add_parameter y (S.shift 2 t)
                             (add_parameter x (S.shift 1 t)
                                (add_parameter illegal_variable_name t env)))  in
            (* We've inserted eventual.z into position 3 of the context, where c wasn't
             * expecting it. So we need to shift all references to variables 3 and up by 1,
             * but leave variables 0, 1, and 2 alone. *)
            let c' = S.shift ~cut:3 1 c  in
            (*let _ = P.debug "!! c' = %s@." (S.string_of_term c')  in*)
            (*let _ = P.debug "!! c' = %t@." (print_term env_c' c')  in*)
            (*let _ = Ctx.print env_c'.ctx in*)
            let _ = match o, infer_ty env_c' c' with
                    | S.Pr, S.NonFib _ ->
                         Error.verify "Eliminating prop equality %t@ in non-fibered family %t"
                             (print_term env q) (print_term env_c' c')
                    | _, _ -> ()  in

            (*let _ = P.debug "!! AFTER infer_ty of c'"  in*)

            let env_w = add_parameter z t env in
            let w_ty_expected = S.beta (S.beta (S.beta c' (S.Refl(o, S.Var 3, S.shift 3 t)))
                                               (S.Var 1))
                                       (S.Var 0)  in

            (*let _ = P.debug "!! w_ty_expected = %s@." (S.string_of_term w_ty_expected)  in*)
            (*let _ = P.debug "!! w_ty_expected = %t@." (print_term env_w w_ty_expected)  in*)

            let _ = check env_w w w_ty_expected  in

            (* We're using c rather than c', so we don't have to worry about
             * that eventual.z variable at all. *)
            S.beta (S.beta (S.beta c
                                   (S.shift 2 q))
                           (S.shift 1 b))
                   a
        end
    | S.MetavarApp mva ->
        begin
          match S.get_mva mva with
          | Some defn -> infer env defn
          | None -> Error.verify ~loc:mva.S.mv_pos "Unset metavariable %s" (S.string_of_mva mva)
        end

and addHandlers env handlers =
  match handlers with
  | [] -> env
  | term :: rest ->
     let e1, e2, _ = infer_eq env term S.Ju in
     P.debug "Adding handler %t = %t@." (print_term env e1) (print_term env e2);
     let installdepth = depth env  in
     let env' = { env with handlers = (installdepth,e1,e2) :: env.handlers } in
     addHandlers env' rest

and infer_ty env term =
  let k = infer env term in
  match as_u env k with
  | S.U u, () -> u
  | _ -> Error.verify "Not a type: %t" (print_term env term)


and infer_eq env term o =
  let ty = infer env term in
  match as_u env ty with
  | S.Eq(o', e1, e2, t), () ->
      if (o = o') then
        e1, e2, t
      else
        Error.verify "Wrong sort of equivalence: %t" (print_term env ty)
  | _ -> Error.verify "Not an equivalence: %t" (print_term env term)



and check env term t =
  match term with

    | S.Handle (term1, handlers) ->
        let env'= addHandlers env handlers in
        check env' term1 t

    | S.Pair (term1, term2) ->
        begin
          match as_sigma env t with
          | S.Sigma(x, t1, t2), () ->
              let _ = check env term1 t1  in
              let t2' = S.beta t2 term1  in
              let _ = check env term2 t2'  in
              ()
          | _ -> Error.verify "Pair cannot have type %t"
                     (print_term env t)
        end

    | S.Lambda (x, term1, term2) ->
      begin
        match as_pi env t with
        | S.Pi (_, ty11, ty12), () ->
          check (add_parameter x ty11 env) term2 ty12
        | _ -> Error.verify "Lambda cannot have type %t"
                 (print_term env t)
      end

    | _ ->
      let t' = infer env term in
        match t with
        | S.U u ->
            begin
              match as_u env t' with
              | S.U u', () when S.universe_le u' u -> ()
              | _ ->
                    Error.verify "expression %t@ has type %t@\nBut should have type %t"
                      (print_term env term) (print_term env t') (print_term env t)
            end
        | _ ->
            begin
              match (Equiv.equal_at_some_universe env t' t ) with
              | None ->
                  Error.verify "expression %t@ has type %t@\nbut should have type %t"
                     (print_term env term) (print_term env t') (print_term env t)
              | Some () -> ()
            end



let inferParam ?(verbose=false) env name term =
  P.debug "@[<hov 4>Verifying %s@ : %s@]@." name (S.string_of_term term);
  let _ = infer_ty env term in
  add_parameter name term env

let inferDefinition env name term termDef =
  P.debug "@[<hov 4>Verifying %s@ : %s@ := %s@]@."
        name (S.string_of_term term) (S.string_of_term termDef);
  let _ = infer_ty env term  in
  let _ = check env termDef term in
  add_definition name term termDef env


let verifyContext ctx =
  let process_decl name decl env =
    match decl with
    | Ctx.Parameter term -> inferParam env name term
    | Ctx.Definition (term1, term2) -> inferDefinition env name term1 term2  in
  let _ = List.fold_right2 process_decl ctx.Ctx.names ctx.Ctx.decls empty_env in
  Format.printf "Verification complete.@."

let instantiate _ _ _ =
  Error.verify "Verification must not instantiate metavariables!"

end
