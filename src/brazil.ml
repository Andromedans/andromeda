

(* Note: It would be nicer to define Ctx here instead of in its own
 *   "BrazilContext" file/module, but Verify needs to refer to Norm
 *   and Norm needs to reference BrazilContext, so Norm would
 *   have to be defined in this file too, or maybe in Equivalence.
 *   And I'm not prepared to do that yet.
 *
 * XXX: Normalization is now in Equivalence! So we could do this...
 *
 * Actually, Ctx should be defined in BrazilSyntax, not here in
 * the verifier! I'm getting my Brazils confused, I think.
 *)


(***********************************)
(** Equivalence Testing for Brazil *)
(***********************************)

module rec Equiv : sig
                     val equal_at_some_universe : Verify.env ->
                            Verify.term -> Verify.term
                            -> Verify.handled_result option
                     val whnf : Verify.env -> Verify.term -> Verify.term
                     val nf : Verify.env -> Verify.term -> Verify.term
                   end =
    Equivalence.Make(Verify)

(****************************)
(* Type Checking for Brazil *)
(****************************)

and Verify : sig

  (* Expose everything that the equivalence algorithm needs *)
  include Equivalence.EQUIV_ARG
    with type handled_result = unit    (* No handler-tracking *)

  (* Needed by top-level TT *)
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
let add_parameters bnds env =
  {env with ctx = Ctx.add_parameters bnds env.ctx}


let lookup v env = Ctx.lookup v env.ctx
let lookup_classifier v env = Ctx.lookup_classifier v env.ctx
let lookup_definition v env = Ctx.lookup_definition v env.ctx
let shift_to_env (env1, exp) env2 = Ctx.shift_to_ctx (env1.ctx, exp) env2.ctx
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
    | [] -> Equiv.whnf env k, ()
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

    | S.Pair (e1, e2, x, ty1, ty2) ->
        begin
          let _ = check env e1 ty1  in
          let _ = check env e2 (S.beta ty2 e1)  in
          S.Sigma("_", ty1, ty2)
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

    | S.Lambda (x, term1, term2, term3) ->
        begin
          let _    = infer_ty env term1 in
          let env' = add_parameter x term1 env  in
          let _    = infer_ty env' term2  in
          let _    = check env' term3 term2 in
          S.Pi(x, term1, term2)
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
            let u_i   = infer_ty env t  in
            let _     = check env a t   in
            let _     = check env b t   in

            (* Check that o and t are compatible, to be sure pathtype is
               well-formed. *)
            let _ =
              match o, u_i with
              | S.Pr, S.NonFib _ ->
                  Error.verify "Ind_eq forming prop equality at non-fibered type %t"
                     (print_term env t)
              | _, _ -> ()  in

            let pathtype = S.Eq(o, a, b, t) in
            let _     = check env q pathtype  in

            let env_xyp, env_z =
               S.create_ind_eq_envs add_parameters env o t (x,y,p) z  in

            let _ = match o, infer_ty env_xyp c with
                    | S.Pr, S.NonFib _ ->
                         Error.verify "Eliminating prop equality %t@ in non-fibered family %t"
                             (print_term env q) (print_term env_xyp c)
                    | _, _ -> ()  in


            let w_ty_expected, ind_eq_type =
              S.create_ind_eq_types env_xyp env_z o t (x,y,p,c) z a b q  in

            let _ = check env_z w w_ty_expected  in

            ind_eq_type
        end
    | S.MetavarApp mva ->
        begin
          match S.get_mva mva with
          | Some defn -> infer env defn
          | None ->
              begin
                let ty = S.get_mva_ty mva in
                let _ = infer_ty env ty  in
                let printable_ty = Equiv.nf env ty  in
                match S.get_mva_sort mva with
                | S.MV_admit ->
                    let loc = S.get_mva_pos mva in
                    Format.printf "@[<hov 4>ADMIT at %s of type@ %t@]@."
                      (Common.string_of_position loc)
                      (print_term env printable_ty);
                    ty
                | S.MV_wildcard ->
                    Error.verify ~loc:mva.S.mv_pos "Unset metavariable %s@ of type %t"
                      (S.string_of_mva mva) (print_term env printable_ty)
              end
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

    | S.Lambda (x, _, _, term3) ->
      begin
        match as_pi env t with
        | S.Pi (_, ty11, ty12), () ->
          check (add_parameter x ty11 env) term3 ty12
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
