(** Type inference. *)

module D = Desugar
module S = Syntax
module Ctx = Context


exception Unimplemented

type size = Small | Large

type synthAnswer =
  | AnsExp  of S.expr * S.ty
  | AnsTy   of S.ty * S.kind
  | AnsKind of S.kind

(** [equal_at ctx e1 e2 t] compares expressions [e1] and [e2] at sort [t]. It is assumed
    that [t] is a valid sort. It is also assumed that [e1] and [e2] have sort [t]. *)
let rec equal_at ctx e1 e2 t =
  let t = Norm.whnf ctx t in
    match t with
      | S.Pi (x, t1, t2) ->
        let e1' = S.mk_app (S.shift 1 e1) (S.mk_var 0) in
        let e2' = S.mk_app (S.shift 1 e2) (S.mk_var 0) in
          equal_at (Ctx.add_parameter x t1 ctx) e1' e2' t2
      | S.Type | S.Sort -> equal_sort ctx e1 e2
      | S.Var _ | S.App _ -> equal ctx e1 e2
      | S.Lambda _ | S.Subst _ | S.Ascribe _ ->
        Error.runtime "internal error, compare at non-sort"

and equal ctx e1 e2 =
  let e1 = Norm.whnf ctx e1 in
  let e2 = Norm.whnf ctx e2 in
    match e1, e2 with
      | S.Type, S.Type -> true
      | S.Sort, S.Sort -> true
      | S.Pi (x, t1, t2), S.Pi (_, s1, s2) ->
        equal_sort ctx t1 s1 &&
        equal_sort (Ctx.add_parameter x t1 ctx) t2 s2
      | S.Var _, S.Var _
      | S.App _, S.App _ -> None <> equal_spine ctx e1 e2
      | (S.Var _ | S.Pi _ | S.Lambda _ | S.App _
            | S.Subst _ | S.Ascribe _ | S.Type | S.Sort), _ -> false

and equal_spine ctx e1 e2 =
  match e1, e2 with
    | S.Var k1, S.Var k2 ->
      if k1 = k2
      then Some (Ctx.lookup_ty k2 ctx)
      else None
    | S.App (a1, a2), S.App (b1, b2) ->
      (match equal_spine ctx a1 b1 with
        | None -> None
        | Some t ->
          (match (Norm.whnf ctx t) with
            | S.Pi (x, u1, u2) ->
              if equal_at ctx a2 b2 u1
              then Some (S.mk_subst (S.Dot (a2, S.idsubst)) u2)
              else None
            | _ -> None))
    | (S.Var _ | S.Pi _ | S.Lambda _ | S.App _ | S.Subst _ | S.Ascribe _ | S.Type | S.Sort), _ -> None

(** [t1] and [t2] must be valid sorts. *)
(*and equal_sort ctx t1 t2 = equal ctx t1 t2*)


(** [inferExp ctx e] infers the type of expression [e] in context [ctx]. *)

let rec inferExp ctx ((_,loc) as term) =
  match (infer ctx term) with
  | AnsExp (e,t) -> (e,t)
  | AnsTy _   -> Error.typing ~loc:loc "Found a type where an expression was expected"
  | AnsKind _ -> Error.typing ~loc:loc "Found a kind where an expression was expected"

and inferTy ctx ((_, loc) as term) =
  match infer ctx term with
  | AnsExp _ -> Error.typing ~loc:loc "Found an expression where a type was expected"
  | AnsTy (t,k) -> (t,k)
  | AnsKind _ -> Error.typing ~loc:loc "Found a kind where a type was expected"


and inferKind ctx ((_, loc) as term) =
  match infer ctx term with
  | AnsExp _ -> Error.typing ~loc:loc "Found an expression where a kind was expected"
  | AnsTy _   -> Error.typing ~loc:loc "Found a type where an kind was expected"
  | AnsKind k -> k

and infer ctx (term, loc) =
  match term with

    | D.Var v ->
        begin
          match Ctx.lookup v ctx with
          | (Ctx.Parameter t | Ctx.Definition (t, _)) -> AnsExp(S.Var v, t)
          | (Ctx.TyParameter k | Ctx.TyDefinition (k, _)) -> AnsTy(S.TVar v, k)
        end

    | D.Pi (x, term1, term2) ->
        begin
          (* The domains of our Pi's are always types, for now *)
          let t1 =
            begin
              match inferTy ctx term1 with
              | t1, S.KType -> t1
              | _, _ -> Error.typing ~loc:loc "Domain of Pi is not a proper type"
            end  in

          let ctx' = Ctx.add_parameter x t1 ctx in

          match infer ctx' term2 with
          | AnsTy (t2, KType) -> AnsTy (S.TPi(x, t1, t2), KType)
          | AnsKind k2        -> AnsKind (S.KPi(x, t1, k2))
          | _ -> Error.typing ~loc:loc "Codomain of Pi is neither a kind nor a proper type"
        end

    | D.App (term1, term2) ->
        begin
          match infer ctx term1 with
          | AnsExp (e1, t1) ->
              begin
                match norm.whnf t1 with
                | S.TPi(_, t11, t12) ->
                    let e2 = checkExp ctx term2 t11  in
                    AnsExp(S.App(e1, e2), S.substTy 0 e2 t12)
                | (S.TVar _ | S.TApp _) ->
                    Error.typing ~loc:loc "Operand does not have a Pi type"
              end
          | AnsTy (t1, k1) ->
              begin
                match k1 with
                | S.KPi(_, t11, k12) ->
                    let e2 = checkExp ctx term2 t11  in
                    AnsTy(S.TApp(t1, e2), S.substKind 0 e2 k12)
                | S.KType ->
                    Error.typing ~loc:loc "Application of a proper type"
              end
          | AnsKind _ -> Error.typing ~loc:loc "Application of a kind"
        end

    | D.Ascribe (term1, term2) ->
        begin
          match infer ctx term2 with
          | AnsTy (t2, S.KType) ->
              let e1 = checkExp ctx term1 t2  in
              AnsExp (e1, t2)
          | AnsKind k2 ->
              let t1 = checkTy ctx term1 k2  in
              AnsTy (t1, k2)
          | AnsExp _->
              Error.typing ~loc:loc "Ascription of an expression"
          | AnsTy _ ->
              Error.typing ~loc:loc "Ascription of a non-proper type"
        end

    | D.Lambda (x, None, _) -> Error.typing ~loc "cannot infer the sort of %s" x

    | D.Lambda (x, Some term1, term2) ->
        begin
          match inferTy ctx term1 with
          | (t1, S.KType) ->
              begin
                let (e2, t2) = inferExp (Ctx.add_parameter x t1 ctx) term2 in
                AnsExp(S.Lambda (x, t1, e2), S.Pi(x, t1, t2))
              end
          | _ -> Error.typing ~loc "Parameter annotation not a proper type"
        end

    | D.Operation _ -> raise Unimplemented
    | D.Handle _ -> raise Unimplemented



and check ctx ((e', loc) as e) t =
  ignore (check_sort ctx t) ;
  match e' with
    | Subst (s, e) -> check ctx (subst s e) t (* XXX avoid rechecking t *)
    | Lambda (x, None, e) ->
      (match (Norm.whnf ctx t) with
        | Pi (x, t1, t2) -> check (Ctx.add_parameter x t1 ctx) e t2
        | _ -> Error.typing ~loc "this expression is a function but should have sort@ %t"
          (Print.expr ctx.names t))
    | Sort -> Error.typing ~loc "Sort does not have sort %t" (Print.expr ctx.names t)
    | Var _ | Lambda (_, Some _, _) | Pi _ | App _ | Ascribe _ | Type ->
      let t' = infer ctx e in
        if not (equal_sort ctx t' t) then
          Error.typing ~loc:(snd e) "this expression has sort %t@ but it should have sort %t"
            (Print.expr ctx.names t') (Print.expr ctx.names t)

(* Returns [Small] if the sort is small and [Large] otherwise. *)
and check_sort ctx (e',loc) =
  match e' with
    | Var k ->
      let t = Ctx.lookup_ty k ctx in
      (match (Norm.whnf ctx t) with
        | Type -> Small
        | Sort -> Large
        | _ -> Error.typing ~loc "this expression has sort %t@ but should be a sort" (Print.expr ctx.names t))
    | Subst (s, e) -> check_sort ctx (subst s e)
    | Lambda _ -> Error.typing ~loc "this expression is a function but should be a sort"
    | Pi (x, t1, t2) ->
      let u1 = check_sort ctx t1 in
      let u2 = check_sort (Ctx.add_parameter x t1 ctx) t2 in
        max_size u1 u2
    | App (e1, e2) ->
      let (x, t1, t2) = infer_pi ctx e1 in
        check ctx e2 t1 ;
        check_sort (Ctx.add_parameter x t1 ctx) t2
    | Ascribe (e1, e2) ->
      check ctx e1 e2 ;
      check_sort ctx e1
    | Type -> Large
    | Sort -> Error.typing ~loc "Sort is not a sort"

and infer_pi ctx e =
  let t = infer ctx e in
    match (Norm.whnf ctx t) with
      | Pi (x, t1, t2) -> (x, t1, t2)
      | Subst _ | Ascribe _ -> assert false
      | Var _ | App _ | Type | Sort | Lambda _ ->
        Error.typing ~loc:(snd e) "this expression has sort %t@ but it should be a function" (Print.expr ctx.names t)
