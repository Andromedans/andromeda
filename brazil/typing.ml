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
        (Syntax.Var k, loc),
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
      let ctx = Context.add_equation e1 u ctx in
      let e4, t = syn_term ctx e4 in
        (Syntax.Equation (e1, u, e4), loc), t
    end

  (* syn-rw-hint *)
  | Input.Rewrite (e1, e4) ->
    begin
      let e1, u = syn_term ctx e1 in
      let ctx = Context.add_rewrite e1 u ctx in
      let e4, t = syn_term ctx e4 in
        (Syntax.Rewrite (e1, u, e4), loc), t
    end

  (* syn-abs *)
  | Input.Lambda (x, t, e) ->
    begin
      let t = is_type ctx t in
      let ctx = Context.add_var x t ctx in
      let e, u = syn_term ctx e in
        (Syntax.Lambda (x, t, u, e), loc),
        (Syntax.Prod (x, t, u), loc)
    end

  (* syn-app *)
  | Input.App (e1, e2) ->
    begin
      let e1, t1 = syn_term ctx e1 in
        match Equal.as_prod ctx t1 with
          | Some (x, t, u) ->
            let e2 = chk_term ctx e2 t in
              (Syntax.App ((x, t, u), e1, e2), loc),
              Syntax.beta_ty u e2
          | None ->
            Error.typing ~loc:(snd e1)
              "this expression is used as a function, but it has type@ %t"
              (print_ty ctx t1)
    end

  (* syn-unit *)
  | Input.UnitTerm ->
      (Syntax.UnitTerm, loc),
      (Syntax.Unit, loc)

  (* syn-idpath *)
  | Input.Idpath e ->
    let e, t = syn_term ctx e in
      (Syntax.Idpath (t, e), loc),
      (Syntax.Paths (t, e, e), loc)

  (* syn-J *)
  | Input.J ((x, y, p, u), (z, e1), e2) ->
    begin
    let e2, t2 = syn_term ctx e2 in
      match Equal.as_paths ctx t2 with

        | Some (t, e3, e4) ->
          let ctx_xyp = Context.add_vars
            [  (x, t);
               (y, t);
               (p, (Syntax.Paths
                      (t,
                       (Syntax.Var (-1) (* x *), Position.nowhere),
                       (Syntax.Var (-2) (* y *), Position.nowhere)),
                    Position.nowhere)) ] ctx  in
          let u = is_fibered ctx_xyp u in
          let ctx_z = Context.add_var z t ctx  in
          let zvar = (Syntax.Var 0, Position.nowhere) in (* ctx, z |- z *)
          let t' = Syntax.weaken_ty 0 t in (* ctx, z |- t type *)
          let u' = Syntax.strengthen_ty u [zvar; zvar; (Syntax.Idpath (t', zvar), Position.nowhere)] in
          let e1 = chk_term ctx_z e1 u' in
            (Syntax.J (t, (x, y, p, u), (z, e1), e2, e3, e4), loc),
            Syntax.strengthen_ty u [e3; e4; e2]

        | None ->
          Error.typing ~loc:(snd e2) "this expression should be a path, but its type is@ %t"
            (print_ty ctx t2)
    end

  (* syn-refl *)
  | Input.Refl e ->
      let e, t = syn_term ctx e  in
      (Syntax.Refl(t,e), loc),
      (Syntax.Id(t,e,e), loc)

  (* syn-name-unit *)
  | Input.NameUnit ->
      (Syntax.NameUnit, loc),
      (Syntax.Universe Universe.zero, loc)


  (* syn-name-universe *)
  | Input.NameUniverse alpha ->
    let beta = Universe.succ alpha  in
     (Syntax.NameUniverse alpha, loc),
     (Syntax.Universe beta, loc)

  (* syn-name-prod *)
  | Input.NameProd(x,e1,e2) ->
      begin
        let e1, t1 = syn_term ctx e1  in
        match Equal.as_universe ctx t1 with
        | Some alpha ->
            begin
              let ctx' = Context.add_var x (Syntax.El (alpha, e1), Position.nowhere) ctx in
              let e2, t2 = syn_term ctx' e2  in
              match Equal.as_universe ctx' t2 with
                | Some beta ->
                  let gamma = Universe.max alpha beta  in
                    ((Syntax.NameProd(alpha, beta, x, e1, e2), loc),
                     (Syntax.Universe gamma, loc))
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
              ((Syntax.Coerce(alpha, beta, e), loc),
               (Syntax.Universe beta, loc))
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
              ((Syntax.NamePaths(alpha, e1, e2, e3), loc),
               (Syntax.Universe alpha, loc))
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
            ((Syntax.NameId(alpha, e1, e2, e3), loc),
             (Syntax.Universe alpha, loc))
      end


and chk_term ctx ((term', loc) as term) t =

  Print.debug "Checking term %s@ against type@ %t@."
      (Input.string_of_term string_of_int term) (print_ty ctx t);

  match term' with

  (* chk-eq-hint *)
  | Input.Equation (e1, e4) ->
      begin
        let e1, u = syn_term ctx e1  in
        let ctx = Context.add_equation e1 u ctx  in
        let e4 = chk_term ctx e4 t in
          (Syntax.Equation(e1, u, e4), loc)
      end

  (* chk-rw-hint *)
  | Input.Rewrite (e1, e4) ->
      begin
        let e1, u = syn_term ctx e1  in
        let ctx = Context.add_rewrite e1 u ctx  in
        let e4 = chk_term ctx e4 t in
          (Syntax.Rewrite(e1, u, e4), loc)
      end

  (* chk-syn *)
  | _ -> let e, u = syn_term ctx term  in
         if (Equal.ty ctx u t) then
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
  let t =
    begin match ty with

      (* tychk-universe *)
      | Input.Universe u -> Syntax.Universe u

      (* tychk-el *)
      | Input.El e ->
        begin
          let (e, t) = syn_term ctx e in
            match Equal.as_universe ctx t with
              | Some alpha -> Syntax.El (alpha, e)
              | None ->
                Error.typing ~loc "tis expression should be a type but it has type@ %t"
                  (print_ty ctx t)
        end

    (* tychk-unit *)
      | Input.Unit -> Syntax.Unit

    (* tychk-prod *)
      | Input.Prod (x, t, u) ->
        let t = is_type ctx t in
        let u = is_type (Context.add_var x t ctx) u in
          Syntax.Prod (x, t, u)

    (* tychk-paths *)
      | Input.Paths (e1, e2) ->
        begin
          let (e1, t) = syn_term ctx e1 in
            match wf_type_is_fibered t with
              | true ->
                let e2 = chk_term ctx e2 t in
                  Syntax.Paths (t, e1, e2)
              | false ->
                Error.typing ~loc "invalid paths because %t is not fibered"
                  (print_ty ctx t)
        end

    (* tychk-id *)
      | Input.Id (e1, e2) ->
        let (e1, t) = syn_term ctx e1 in
        let e2 = chk_term ctx e2 t in
          Syntax.Paths (t, e1, e2)
    end
  in
    (t, loc)

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

