(********************)
(* Helper Functions *)
(********************)

let print_ty ctx ty =
  Print.ty (Context.names ctx) ty

let print_term ctx term =
  Print.term (Context.names ctx) term

let print_universe = Print.universe

(***********************************)
(* Synthesis and Checking of Terms *)
(***********************************)


let rec syn_term ctx ((term', loc) as term) =

  Print.debug "Synthesizing term %s@."
      (Input.string_of_term string_of_int term);

  match term' with

  (* syn-var *)
  | Input.Var k ->
    begin
      let t = Context.lookup_var k ctx in
        Syntax.mkVar ~loc k,
        t
    end

  (* syn-ascribe *)
  | Input.Ascribe (e,t) ->
      let t = is_type ctx t  in
      let e = chk_term ctx e t  in
        e,
        t

  (* syn-eq-hint *)
  | Input.Equation (e1, e4) ->
    begin
      let e1, u = syn_term ctx e1 in
      let h = Equal.as_hint ctx e1 u in
      let ctx = Context.add_equation h ctx in
      let e4, t = syn_term ctx e4 in
        (Syntax.mkEquation ~loc e1 u e4), t
    end

  (* syn-rw-hint *)
  | Input.Rewrite (e1, e4) ->
    begin
      let e1, u = syn_term ctx e1 in
      let h = Equal.as_hint ctx e1 u in
      let ctx = Context.add_rewrite h ctx in
      let e4, t = syn_term ctx e4 in
        (Syntax.mkRewrite ~loc e1 u e4), t
    end

  (* syn-abs *)
  | Input.Lambda (x, t, e) ->
    begin
      let t = is_type ctx t in
      let ctx = Context.add_var x t ctx in
      let e, u = syn_term ctx e in
        (Syntax.mkLambda ~loc x t u e),
        (Syntax.mkProd ~loc x t u)
    end

  (* syn-app *)
  | Input.App (e1, e2) ->
    begin
      let e1, t1 = syn_term ctx e1 in
        match Equal.as_prod ctx t1 with
          | Some (x, t, u) ->
            let e2 = chk_term ctx e2 t in
              Syntax.mkApp ~loc x t u e1 e2,
              Syntax.beta_ty u e2
          | None ->
            Error.typing ~loc:(snd e1)
              "this expression is used as a function, but it has type@ %t"
              (print_ty ctx t1)
    end

  (* syn-unit *)
  | Input.UnitTerm ->
      Syntax.mkUnitTerm ~loc (),
      Syntax.mkUnit ~loc ()

  (* syn-idpath *)
  | Input.Idpath e ->
    let e, t = syn_term ctx e in
      Syntax.mkIdpath ~loc t e,
      Syntax.mkPaths ~loc t e e

  (* syn-J *)
  | Input.J ((x, y, p, u), (z, e1), e2) ->
    begin
    let e2, t2 = syn_term ctx e2 in
      match Equal.as_paths ctx t2 with

        | Some (t, e3, e4) ->
          let ctx_xyp, ctx_z = Context.for_J t x y p z ctx in
          let u = is_fibered ctx_xyp u in
          let zvar = Syntax.mkVar 0 in (* ctx, z |- z *)
          let t' = Syntax.weaken_ty 0 t in (* ctx, z |- t type *)
          let u' = Syntax.strengthen_ty u [zvar; zvar; Syntax.mkIdpath t' zvar] in
          let e1 = chk_term ctx_z e1 u' in
            Syntax.mkJ ~loc t (x, y, p, u) (z, e1) e2 e3 e4,
            Syntax.strengthen_ty u [e3; e4; e2]

        | None ->
          Error.typing ~loc:(snd e2) "this expression should be a path, but its type is@ %t"
            (print_ty ctx t2)
    end

  (* syn-refl *)
  | Input.Refl e ->
      let e, t = syn_term ctx e  in
      Syntax.mkRefl ~loc t e,
      Syntax.mkId ~loc t e e

  (* syn-name-unit *)
  | Input.NameUnit ->
      Syntax.mkNameUnit ~loc (),
      Syntax.mkUniverse ~loc Universe.zero


  (* syn-name-universe *)
  | Input.NameUniverse alpha ->
    let beta = Universe.succ alpha  in
     Syntax.mkNameUniverse ~loc alpha,
     Syntax.mkUniverse ~loc beta

  (* syn-name-prod *)
  | Input.NameProd(x,e1,e2) ->
      begin
        let e1, t1 = syn_term ctx e1  in
        match Equal.as_universe ctx t1 with
        | Some alpha ->
            begin
              let ctx' = Context.add_var x (Syntax.mkEl alpha e1) ctx in
              let e2, t2 = syn_term ctx' e2  in
              match Equal.as_universe ctx' t2 with
                | Some beta ->
                  let gamma = Universe.max alpha beta  in
                    Syntax.mkNameProd ~loc alpha beta x e1 e2,
                    Syntax.mkUniverse ~loc gamma
                | None ->
                  Error.typing ~loc:(snd e2) "this expression should be a type, but it has type@ %t"
                    (print_ty ctx t2)
            end
        | None ->
            Error.typing ~loc:(snd e1) "this expression should be a type, but it has type@ %t"
               (print_ty ctx t1)
      end

  (* syn-name-coerce *)
  | Input.Coerce(beta, e) ->
      begin
        let e, t = syn_term ctx e  in
        match Equal.as_universe ctx t with
        | Some alpha ->
            if Universe.leq alpha beta then
              Syntax.mkCoerce ~loc alpha beta e,
              Syntax.mkUniverse ~loc beta
            else
              Error.typing ~loc "cannot coerce from universe@ %t@ to universe %t"
                 (print_universe alpha)
                 (print_universe beta)
        | None ->
            Error.typing ~loc "this expression should be a type,, but it has type@ %t"
               (print_ty ctx t)
      end

  (* syn-name-paths *)
  | Input.NamePaths (e2, e3) ->
     begin
        let e2, t2 = syn_term ctx e2  in
        match Syntax.name_of t2 with
        | None ->
          Error.typing ~loc:(snd e2) "this expression should be a fibered type but its type is %t"
            (print_ty ctx t2)
        | Some (e1, alpha) ->
            if (Universe.is_fibered alpha) then
              let e3 = chk_term ctx e3 t2 in
              Syntax.mkNamePaths ~loc alpha e1 e2 e3,
              Syntax.mkUniverse ~loc alpha
            else
              Error.typing ~loc "this expression should be a fibered type, but its type is %t"
                (print_ty ctx t2)
      end

  (* syn-name-id *)
  | Input.NameId(e2,e3) ->
      begin
        let e2, t2 = syn_term ctx e2  in
        match Syntax.name_of t2 with
        | None -> Error.typing ~loc "this expression should be a type but its type is %t"
                         (print_ty ctx t2)
        | Some (e1, alpha) ->
            let e3 = chk_term ctx e3 t2 in
            Syntax.mkNameId ~loc alpha e1 e2 e3,
            Syntax.mkUniverse ~loc alpha
      end


and chk_term ctx ((term', loc) as term) t =

  Print.debug "Checking term %s@ against type@ %t@."
      (Input.string_of_term string_of_int term) (print_ty ctx t);

  match term' with

  (* chk-eq-hint *)
  | Input.Equation (e1, e4) ->
      begin
        let e1, u = syn_term ctx e1  in
        let h = Equal.as_hint ctx e1 u in
        let ctx = Context.add_equation h ctx  in
        let e4 = chk_term ctx e4 t in
        Syntax.mkEquation ~loc e1 u e4
      end

  (* chk-rw-hint *)
  | Input.Rewrite (e1, e4) ->
      begin
        let e1, u = syn_term ctx e1  in
        let h = Equal.as_hint ctx e1 u in
        let ctx = Context.add_rewrite h ctx  in
        let e4 = chk_term ctx e4 t in
        Syntax.mkRewrite ~loc e1 u e4
      end

  (* chk-syn *)
  | _ -> let e, u = syn_term ctx term  in
         if (Equal.equal_ty ctx u t) then
            e
         else
            Error.typing ~loc "expression@ %t@;<1 -2>has type@ %t@;<1 -2>but should have type %t"
              (print_term ctx e)
              (print_ty ctx u)
              (print_ty ctx t)

(***********************************)
(* Synthesis and Checking of Types *)
(***********************************)


(* Can the given unannotated type be verified and translated into an annotated type?
 *)
and is_type ctx (ty, loc) =
    begin match ty with

      (* tychk-universe *)
      | Input.Universe u -> Syntax.mkUniverse ~loc u

      (* tychk-el *)
      | Input.El e ->
        begin
          let (e, t) = syn_term ctx e in
            match Equal.as_universe ctx t with
              | Some alpha -> Syntax.mkEl ~loc alpha e
              | None ->
                Error.typing ~loc "this expression should be a type but it has type@ %t"
                  (print_ty ctx t)
        end

    (* tychk-unit *)
      | Input.Unit -> Syntax.mkUnit ~loc ()

    (* tychk-prod *)
      | Input.Prod (x, t, u) ->
        let t = is_type ctx t in
        let u = is_type (Context.add_var x t ctx) u in
          Syntax.mkProd ~loc x t u

    (* tychk-paths *)
      | Input.Paths (e1, e2) ->
        begin
          let (e1, t) = syn_term ctx e1 in
            match wf_type_is_fibered t with
              | true ->
                let e2 = chk_term ctx e2 t in
                  Syntax.mkPaths ~loc t e1 e2
              | false ->
                Error.typing ~loc "invalid paths because %t is not fibered"
                  (print_ty ctx t)
        end

    (* tychk-id *)
      | Input.Id (e1, e2) ->
        let (e1, t) = syn_term ctx e1 in
        let e2 = chk_term ctx e2 t in
          Syntax.mkId ~loc t e1 e2
    end

(* Can the given unannotated type be verified and translated into an annotated fibered type?
 *)
and is_fibered ctx ((_, loc) as ty) =
  let annotated_ty = is_type ctx ty   in
  if wf_type_is_fibered annotated_ty then
    annotated_ty
  else
    Error.typing ~loc "expected a fibered type but found@ %t"
         (print_ty ctx annotated_ty)

(* wf_type_is_fibered: Syntax.ty -> bool
    Is the given well-formed type also a fibered type?
*)
and wf_type_is_fibered (ty', _) =
  match ty' with
  | Syntax.Universe alpha -> Universe.is_fibered alpha
  | Syntax.Prod(_, t, u) ->
      wf_type_is_fibered t && wf_type_is_fibered u
  | Syntax.El(alpha, _) -> Universe.is_fibered alpha
  | Syntax.Unit -> true
  | Syntax.Paths _ -> true
  | Syntax.Id _ -> false

(***********)
(* type_of *)
(***********)

let rec type_of ctx (exp, _) =
  let loc = Position.nowhere in
  match exp with
  | Syntax.Var v -> Context.lookup_var v ctx
  | Syntax.Equation (_, _, body)
  | Syntax.Rewrite (_, _, body) -> type_of ctx body
  | Syntax.Ascribe (_, ty) -> ty
  | Syntax.Lambda (x, t1, t2, _) -> Syntax.Prod(x, t1, t2), loc
  | Syntax.App ((_, _, t2), _, e2) -> Syntax.beta_ty t2 e2
  | Syntax.UnitTerm -> Syntax.Unit, loc
  | Syntax.Idpath (t, e) -> Syntax.Paths(t, e, e), loc
  | Syntax.J (_, (_, _, _, u), _, e2, e3, e4) -> Syntax.strengthen_ty u [e2; e3; e4]
  | Syntax.Refl (t, e) -> Syntax.Id(t, e, e), loc
  | Syntax.Coerce (_, beta, _) -> Syntax.Universe beta, loc
  | Syntax.NameUnit -> Syntax.Universe Universe.zero, loc
  | Syntax.NameProd (alpha, beta, _, _, _) -> Syntax.Universe (Universe.max alpha beta), loc
  | Syntax.NameUniverse alpha -> Syntax.Universe (Universe.succ alpha), loc
  | Syntax.NamePaths (alpha, _, _, _)
  | Syntax.NameId    (alpha, _, _, _) -> Syntax.Universe alpha, loc


