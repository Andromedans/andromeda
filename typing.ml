(** Type inference. *)

module D = Desugar
module S = Syntax
module Ctx = Context


(* Possible answers when doing type inference on a "term"
 *)
type synthAnswer =
  | AnsExp  of S.expr * S.ty
  | AnsTy   of S.ty * S.kind
  | AnsKind of S.kind

type env = {
  ctx : Ctx.context;
  handlers : (int * S.operation * S.computation) list;  (* install-level *)
}

let empty_env = { ctx = Ctx.empty_context;
                  handlers = [];
                 }

let add_parameter x t env =
  {env with ctx = Ctx.add_parameter x t env.ctx}
let add_ty_parameter x k env =
  {env with ctx = Ctx.add_ty_parameter x k env.ctx}
let add_definition x t e env =
  {env with ctx = Ctx.add_definition x t e env.ctx}
let add_ty_definition x k t env =
  {env with ctx = Ctx.add_ty_definition x k t env.ctx}

let lookup v env = Ctx.lookup v env.ctx
let lookup_ty v env = Ctx.lookup_ty v env.ctx
let lookup_kind v env = Ctx.lookup_kind v env.ctx

let currentLevel env = List.length env.ctx.Ctx.names

(** [equal_at env e1 e2 t] compares expressions [e1] and [e2] at sort [t]. It is assumed
    that [t] is a valid sort. It is also assumed that [e1] and [e2] have sort [t]. *)
let rec equal_at env e1 e2 t =
  S.equal (Norm.nf env.ctx e1) (Norm.nf env.ctx e2)

  (*
  let t = Norm.whnf env t in
    match t with
      | S.Var k1, S.Var k2 -> (k1 = k2)
      | S.
      | S.TPi (x, t1, t2) ->
        let e1' = S.mk_app (S.shift 1 e1) (S.mk_var 0) in
        let e2' = S.mk_app (S.shift 1 e2) (S.mk_var 0) in
          equal_at (add_parameter x t1 env) e1' e2' t2
      | S.TVar _ | S.TApp _ -> equal env e1 e2

and equal env e1 e2 =
  let e1 = Norm.whnf env e1 in
  let e2 = Norm.whnf env e2 in
    match e1, e2 with
      | S.TPi (x, t1, t2), S.Pi (_, s1, s2) ->
        equal_sort env t1 s1 &&
        equal_sort (add_parameter x t1 env) t2 s2
      | S.Var _, S.Var _
      | S.App _, S.App _ -> None <> equal_spine env e1 e2
      | (S.Var _ | S.Pi _ | S.Lambda _ | S.App _
            | S.Subst _ | S.Ascribe _ | S.Type | S.Sort), _ -> false

and equal_spine env e1 e2 =
  match e1, e2 with
    | S.Var k1, S.Var k2 ->
      if k1 = k2
      then Some (lookup_ty k2 env)
      else None
    | S.App (a1, a2), S.App (b1, b2) ->
      (match equal_spine env a1 b1 with
        | None -> None
        | Some t ->
          (match (Norm.whnf env t) with
            | S.Pi (x, u1, u2) ->
              if equal_at env a2 b2 u1
              then Some (S.mk_subst (S.Dot (a2, S.idsubst)) u2)
              else None
            | _ -> None))
    | (S.Var _ | S.Pi _ | S.Lambda _ | S.App _ | S.Subst _ | S.Ascribe _ | S.Type | S.Sort), _ -> None
    *)

and equalTy_at env t1 t2 k =
  match k with
      | S.KPi (x, t3, k3) ->
          let t1' = S.TApp (S.shiftTy 1 t1, S.Var 0) in
          let t2' = S.TApp (S.shiftTy 1 t2, S.Var 0) in
          equalTy_at (add_parameter x t3 env) t1' t2' k3
      | S.KType ->
          begin
            let t1' = Norm.whnfTy env.ctx t1 in
            let t2' = Norm.whnfTy env.ctx t2 in
            match equalTy_spine env t1' t2' with
            | Some _ -> true
            | _      -> false
          end

and equalTy_spine env t1 t2 =
  match t1, t2 with
  | S.TVar v1, S.TVar v2 ->
      if v1 = v2 then Some (lookup_kind v1 env) else None
  | S.TPi (x, t11, t12), S.TPi (_, t21, t22) ->
      if ( equalTy_at env t11 t21 S.KType &&
           equalTy_at (add_parameter x t11 env) t12 t22 S.KType ) then
        Some S.KType
      else
        None
  | S.TSigma (x, t11, t12), S.TSigma (_, t21, t22) ->
      if ( equalTy_at env t11 t21 S.KType &&
           equalTy_at (add_parameter x t11 env) t12 t22 S.KType ) then
        Some S.KType
      else
        None
  | S.TApp (p1, e1), S.TApp (p2, e2) ->
      begin
        match equalTy_spine env p1 p2 with
        | Some (S.KPi (_, t3, k3)) ->
            if (equal_at env e1 e2 t3) then
              Some (S.betaKind k3 e1)
            else
              None
        | _ -> None
      end

  | S.TEquiv(e11, e12, t1), S.TEquiv(e21, e22, t2) ->
      begin
        if (equalTy_at env t1 t2 S.KType) &&
           (equal_at env e11 e21 t1) &&
           (equal_at env e12 e22 t1) then
          Some S.KType
        else
          None
      end

  | S.TEquivTy(t11, t12, k1), S.TEquivTy(t21, t22, k2) ->
      begin
        if (equalKind env k1 k2) &&
           (equalTy_at env t11 t21 k1) &&
           (equalTy_at env t12 t22 k1) then
          Some S.KType
        else
          None
      end


  | (S.TVar _ | S.TPi _ | S.TSigma _ | S.TApp _ | S.TEquiv _ | S.TEquivTy _ ), _ -> None

and equalKind env k1 k2 =
  match k1, k2 with
  | S.KType, S.KType -> true
  | S.KPi(x, t1, k1'), S.KPi(_, t2, k2') ->
      ( equalTy_at env t1 t2 S.KType &&
        equalKind (add_parameter x t1 env) k1' k2' )

  | (S.KType | S.KPi _), _ -> false


(** [t1] and [t2] must be valid sorts. *)
(*and equal_sort env t1 t2 = equal env t1 t2*)


(** [inferExp env e] infers the type of expression [e] in context [env]. *)

let rec inferExp env ((_,loc) as term) =
  match (infer env term) with
  | AnsExp (e,t) -> (e,t)
  | AnsTy _   -> Error.typing ~loc "Found a type where an expression was expected"
  | AnsKind _ -> Error.typing ~loc "Found a kind where an expression was expected"

and inferTy env ((_, loc) as term) =
  match infer env term with
  | AnsExp _ -> Error.typing ~loc "Found an expression where a type was expected"
  | AnsTy (t,k) -> (t,k)
  | AnsKind _ -> Error.typing ~loc "Found a kind where a type was expected"


and inferKind env ((_, loc) as term) =
  match infer env term with
  | AnsExp _ -> Error.typing ~loc "Found an expression where a kind was expected"
  | AnsTy _   -> Error.typing ~loc "Found a type where an kind was expected"
  | AnsKind k -> k

and infer env (term, loc) =
  match term with

    | D.Var v ->
        begin
          match lookup v env with
          | (Ctx.Parameter t | Ctx.Definition (t, _)) -> AnsExp(S.Var v, t)
          | (Ctx.TyParameter k | Ctx.TyDefinition (k, _)) -> AnsTy(S.TVar v, k)
        end

    | D.Pi (x, term1, term2) ->
        begin
          (* The domains of our Pi's are always types, for now *)
          let t1 =
            begin
              match inferTy env term1 with
              | t1, S.KType -> t1
              | _, _ -> Error.typing ~loc "Domain of Pi is not a proper type"
            end  in

          let env' = add_parameter x t1 env in

          match infer env' term2 with
          | AnsTy (t2, S.KType) -> AnsTy (S.TPi(x, t1, t2), S.KType)
          | AnsKind k2          -> AnsKind (S.KPi(x, t1, k2))
          | _ -> Error.typing ~loc "Codomain of Pi is neither a kind nor a proper type"
        end

    | D.Sigma (x, term1, term2) ->
        begin
          (* The domains of our Sigmas are always types, for now *)
          let t1 =
            begin
              match inferTy env term1 with
              | t1, S.KType -> t1
              | _, _ -> Error.typing ~loc "Domain of Sigma is not a proper type"
            end  in

          let env' = add_parameter x t1 env in

          match infer env' term2 with
          | AnsTy (t2, S.KType) -> AnsTy (S.TSigma(x, t1, t2), S.KType)
          | _ -> Error.typing ~loc "Codomain of Sigma is not a proper type"
        end

    | D.App (term1, term2) ->
        begin
          match infer env term1 with
          | AnsExp (e1, t1) ->
              begin
                (* Application of two expressions *)
                match Norm.whnfTy env.ctx t1 with
                | S.TPi(_, t11, t12) ->
                    let e2 = checkExp env term2 t11  in
                    let appTy = S.betaTy t12 e2  in
                    AnsExp( S.App(e1, e2), appTy )
                | (S.TVar _ | S.TApp _ | S.TSigma _ | S.TEquiv _ | S.TEquivTy _ ) ->
                    Error.typing ~loc "Operand does not have a Pi type"
              end

          | AnsTy (t1, k1) ->
              begin
                (* Application of a type to an expression *)
                match k1 with
                | S.KPi(_, t11, k12) ->
                    let e2 = checkExp env term2 t11  in
                    let appKind = S.betaKind k12 e2 in
                    AnsTy(S.TApp(t1, e2), appKind)
                | S.KType ->
                    Error.typing ~loc "Application of a proper type"
              end

          | AnsKind _ -> Error.typing ~loc "Application of a kind"
        end

    | D.Pair (term1, term2) ->
        begin
          let e1, t1 = inferExp env term1  in
          let e2, t2 = inferExp env term2  in
          let ty = S.TSigma("_", t1, S.shiftTy 1 t2)  in
          AnsExp( S.Pair(e1,e2), ty )
        end

    | D.Proj (("1"|"fst"), term2) ->
        begin
          let e2, t2 = inferExp env term2  in
          match (Norm.whnfTy env.ctx t2) with
          | S.TSigma(_, t21, _) ->
              AnsExp(S.Proj(1, e2), t21)
          | (S.TVar _ | S.TApp _ | S.TPi _ | S.TEquiv _ | S.TEquivTy _) ->
              Error.typing ~loc "Operand of projection does not have a Sigma type"
        end

    | D.Proj (("2"|"snd"), term2) ->
        begin
          let e2, t2 = inferExp env term2  in
          match (Norm.whnfTy env.ctx t2) with
          | S.TSigma(_, _, t22) ->
              AnsExp(S.Proj(2, e2),
                     S.betaTy t22 (S.Proj(1, e2)))
          | (S.TVar _ | S.TApp _ | S.TPi _ | S.TEquiv _ | S.TEquivTy _) ->
              Error.typing ~loc "Operand of projection does not have a Sigma type"
        end

    (* EXPERIMENTAL *)
    | D.Proj ("type", term2) ->
        begin
          let _, t2 = inferExp env term2  in
          AnsTy(t2, S.KType)
        end

    | D.Proj("dom", term2) ->
        begin
          let domTy =
            match infer env term2 with
            | AnsExp(_, t)
            | AnsTy(t,_ ) ->
                begin
                  match Norm.whnfTy env.ctx t with
                  | S.TPi(_, domTy, _) -> domTy
                  | _ -> Error.typing ~loc "Operand of projection has no domain"
                end
            | AnsKind k ->
                begin
                  match Norm.whnfKind env.ctx k with
                  | S.KPi(_, domTy, _) -> domTy
                  | _ -> Error.typing ~loc "Operand of projection has no domain"
                end
          in
            AnsTy(domTy, S.KType)
        end

    (* END EXPERIMENTAL *)


    | D.Proj (s1, _) -> Error.typing ~loc "Unrecognized projection %s" s1

    | D.Ascribe (term1, term2) ->
        begin
          match infer env term2 with
          | AnsTy (t2, S.KType) ->
              let e1 = checkExp env term1 t2  in
              AnsExp (e1, t2)
          | AnsKind k2 ->
              let t1 = checkTy env term1 k2  in
              AnsTy (t1, k2)
          | AnsExp _->
              Error.typing ~loc "Ascription of an expression"
          | AnsTy _ ->
              Error.typing ~loc "Ascription of a non-proper type"
        end

    | D.Lambda (x, None, _) -> Error.typing ~loc "cannot infer the sort of %s" x

    | D.Lambda (x, Some term1, term2) ->
        begin
          match inferTy env term1 with
          | (t1, S.KType) ->
              begin
                let (e2, t2) = inferExp (add_parameter x t1 env) term2 in
                AnsExp(S.Lambda (x, t1, e2), S.TPi(x, t1, t2))
              end
          | _ -> Error.typing ~loc "Parameter annotation not a proper type"
        end

    | D.Operation (tag, terms) ->
        let operation = inferOp env loc tag terms  in
        inferHandler env loc operation

    | D.Handle (term, handlers) ->
        let env'= addHandlers env loc handlers in
        infer env' term

    | D.Type -> AnsKind S.KType

    | D.Equiv(term1, term2, term3) ->
        begin
          match infer env term3 with
          | AnsKind kind ->
              let ty1 = checkTy env term1 kind  in
              let ty2 = checkTy env term2 kind  in
              AnsTy (S.TEquivTy (ty1, ty2, kind), S.KType)

          | AnsTy (ty, S.KType) ->
              let e1 = checkExp env term1 ty  in
              let e2 = checkExp env term2 ty  in
              AnsTy (S.TEquiv (e1, e2, ty), S.KType)

          | AnsTy _ ->
              Error.typing ~loc "No equivalence at a non-proper type"

          | AnsExp _ ->
              Error.typing ~loc "Equivalence must be at a type or kind"
        end

and inferOp env loc tag terms =
  match tag, terms with
  | D.Inhabit, [term] ->
      begin
        match infer env term with
        | AnsTy (ty, S.KType) -> S.InhabitTy ty
        | AnsTy _ -> Error.typing ~loc "Not a proper type"
        | AnsKind kind -> S.InhabitKind kind
        | AnsExp _ -> Error.typing ~loc "Cannot inhabit an expression"
      end

  | D.Inhabit, _ -> Error.typing ~loc "Wrong number of arguments to INHABIT"

  | D.Coerce, [term1; term2] ->
      let t1 = checkTy env term1 S.KType  in
      let t2 = checkTy env term2 S.KType  in
      S.Coerce(t1, t2)

  | D.Coerce, _ -> Error.typing ~loc "Wrong number of arguments to EQUIV"

and addHandlers env loc handlers =
  let installLevel = currentLevel env  in
  let rec loop = function
    | [] -> env
    | (tag, terms, handlerBody) :: rest ->
        (* When we add patterns, we won't be able to use inferOp any more... *)
        let operation = inferOp env loc tag terms  in
        let env' = { env with handlers = ((installLevel, operation, handlerBody) :: env.handlers) } in
        addHandlers env' loc rest  in
  loop handlers

and checkExp env ((term1, loc) as term) t =
  match term1, Norm.whnfTy env.ctx t with
    | D.Lambda (x, None, term2), S.TPi (_, t1, t2) ->
        begin
          let e2 = checkExp (add_parameter x t1 env) term2 t2 in
          S.Lambda(x, t1, e2)
        end
    | D.Pair (term1, term2), S.TSigma(x, t1, t2) ->
        let e1 = checkExp env term1 t1  in
        let t2' = S.betaTy t2 e1  in
        let e2 = checkExp env term2 t2'  in
        S.Pair(e1, e2)
    | _, _ ->
      let (e, t') = inferExp env term in
        if not (equalTy_at env t' t S.KType) then
          Error.typing ~loc "this expression has type %t@ but it should have type %t"
            (Print.ty env.ctx.Ctx.names t') (Print.ty env.ctx.Ctx.names t)
        else
          e

and checkTy env ((_, loc) as term) k =
  let (t, k') = inferTy env term  in
  if (equalKind env k k') then
    t
  else
    Error.typing ~loc "This type does not have the expected kind"


(* Find the first matching handler, and return the typechecked right-hand-side
 *)
and inferHandler env loc op =
  let level = currentLevel env  in
  let rec loop = function
    | [] -> Error.typing ~loc "Unhandled operation"
    | (installLevel, op1, comp1)::rest ->
        let d = level - installLevel in
        let op1 = Syntax.shiftOperation d op1  in
        if (op = op1) then
          begin
            (* comp1' is the right-hand-size of the handler,
             * shifted so that its free variables are correct
             * in the context where the operation occurred.
             *)
            let comp1' = D.shift d comp1  in

            let ans = match op with
              | S.InhabitTy ty ->
                  AnsExp (checkExp env comp1' ty, ty)
              | S.InhabitKind kind ->
                  AnsTy (checkTy env comp1' kind, kind)
              | S.Coerce (ty1, ty2) ->
                  let ty = S.TPi("_", ty1, S.shiftTy 1 ty2)  in
                  AnsExp (checkExp env comp1' ty, ty)  in
            ans

          end
        else
          loop rest
  in
    loop (env.handlers)



let inferParam ?(verbose=false) env names ((_,loc) as term) =
  match infer env term with
    | AnsExp _ -> Error.typing ~loc "Parameter given with an expression"
    | AnsTy (ty, S.KType) ->
        let env, _ = List.fold_left
          (fun (env, t) name ->
            (*if List.mem x ctx.names then Error.typing ~loc "%s already exists" x ;*)
            if verbose then Format.printf "Term %s is assumed.@." name ;
            (add_parameter name t env, Syntax.shiftTy 1 t))
          (env, ty) names
        in
          env
    | AnsTy (ty, S.KPi _) ->
        Error.typing ~loc "Parameter given with a non-proper type."
    | AnsKind kind ->
        let env, _ = List.fold_left
          (fun (env, k) name ->
            (*if List.mem x ctx.names then Error.typing ~loc "%s already exists" x ;*)
            if verbose then Format.printf "Type %s is assumed.@." name ;
            (add_ty_parameter name k env, Syntax.shiftKind 1 k))
          (env, kind) names
        in
          env

let inferDefinition ?(verbose=false) env name ((_,loc) as termDef) =
  match infer env termDef with
  | AnsTy (ty, kind) ->
      begin
        if verbose then Format.printf "Type %s is defined.@." name;
        add_ty_definition name kind ty env
      end
  | AnsKind kind ->
      Error.typing ~loc "Cannot define kind variables"
  | AnsExp (expr, ty) ->
      begin
        if verbose then Format.printf "Term %s is defined.@." name;
        add_definition name ty expr env;
      end

let inferAnnotatedDefinition ?(verbose=false) env name ((_,loc) as term) termDef =
  match infer env term with
  | AnsTy (ty, S.KType) ->
      let expr = checkExp env termDef ty  in
      add_definition name ty expr env
  | AnsKind kind ->
      let ty = checkTy env termDef kind  in
      add_ty_definition name kind ty env
  | AnsExp _->
      Error.typing ~loc "Not a type or a kind"
  | AnsTy _ ->
      Error.typing ~loc "Not a proper type"



