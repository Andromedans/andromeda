(** Strong normalization that ignores hints. *)

let rec ty ((t', loc) as t) : Syntax.ty =
  match t' with

  (* norm-ty-universe *)
  | Syntax.Universe _ -> t

  | Syntax.El (alpha, e) ->
    begin match term e with

      (* norm-ty-el-coerce *)
      | (Syntax.Coerce (beta, gamma, e), _)
          when Universe.eq alpha gamma ->
        ty (Syntax.El (beta, e), loc)

      (* norm-ty-el-unit *)
      | (Syntax.NameUnit, _)
          when Universe.eq alpha Universe.zero ->
        (Syntax.Unit, loc)

      (* norm-ty-el-prod *)
      | (Syntax.NameProd (beta, gamma, x, e1, e2), _)
          when Universe.eq (Universe.max beta gamma) alpha ->
        let t1 = ty (Syntax.El (beta, e1), snd e1) in
        let t2 = ty (Syntax.El (gamma, e2), snd e2) in
          (Syntax.Prod (x, t1, t2), loc)

      (* norm-ty-el-universe *)
      | (Syntax.NameUniverse beta, _)
          when Universe.eq (Universe.succ beta) alpha ->
        (Syntax.Universe alpha, loc)

      (* norm-ty-el-paths *)
      | (Syntax.NamePaths (beta, e1, e2, e3), _)
          when Universe.eq beta alpha ->
        let t1 = ty (Syntax.El (alpha, e1), loc) in
        let e2' = term e2 in
        let e3' = term e3 in
          (Syntax.Paths (t1, e2', e3'), loc)

      (* norm-ty-el-id *)
      | (Syntax.NameId (beta, e1, e2, e3), _)
          when Universe.eq beta alpha ->
        let t1 = ty (Syntax.El (alpha, e1), loc) in
        let e2' = term e2 in
        let e3' = term e3 in
          (Syntax.Id (t1, e2', e3'), loc)

      (* norm-ty-el-other *)
      | e ->
        (Syntax.El (alpha, e), loc)        
    end

  (* norm-ty-unit *)
  | Syntax.Unit -> t

  (* norm-ty-prod *)
  | Syntax.Prod (x, t, u) ->
    let t' = ty t in
    let u' = ty u in
      (Syntax.Prod (x, t', u'), loc)

  (* norm-ty-paths *)
  | Syntax.Paths (t, e1, e2) ->
    let t' = ty t in
    let e1' = term e1 in
    let e2' = term e2 in
      (Syntax.Paths (t', e1', e2'), loc)

  (* norm-ty-id *)
  | Syntax.Id (t, e1, e2) ->
    let t' = ty t in
    let e1' = term e1 in
    let e2' = term e2 in
      (Syntax.Id (t', e1', e2'), loc)


and term ((e', loc) as e) : Syntax.term =
  match e' with

    (* norm-var *)    
    | Syntax.Var _ ->
      e

    (* norm-advice *)
    | Syntax.Advice (_, _, e) ->
      term e

    (* norm-equation *)
    | Syntax.Equation (_e1, (_e2, _e3), e4) ->
      term e4

    (* norm-rewrite *)
    | Syntax.Rewrite (_e1, (_e2, _e3), e4) ->
      term e4

    (* norm-ascribe *)
    | Syntax.Ascribe (e, _t) ->
      term e

    (* norm-star *)
    | Syntax.UnitTerm -> e

    (* norm-abs *)
    | Syntax.Lambda (x, t1, t2, e) ->
      let t1' = ty t1 in
      let t2' = ty t2 in
      let e' = term e in
        (Syntax.Lambda (x, t1', t2', e'), loc)

    | Syntax.App ((x, t1, t2), e1, e2) ->
      let t1' = ty t1 in
      let t2' = ty t2 in
        begin match term e1 with

          (* norm-app-redex *)
          | (Syntax.Lambda (_, u1, u2, e1'), _)
              when Syntax.equal_ty t1' u1 && Syntax.equal_ty t2' u2 ->
            let e2' = term e2 in
              term (Syntax.beta e1' e2')

          (* norm-app-other *)
          | e1' ->
            let e2' = term e2 in
              (Syntax.App ((x, t1', t2'), e1', e2'), loc)
        end

    (* norm-idpath *)
    | Syntax.Idpath (t, e) ->
      let t' = ty t in
      let e' = term e in
        (Syntax.Idpath (t', e'), loc)

    (* norm-refl *)
    | Syntax.Refl (t, e) ->
      let t' = ty t in
      let e' = term e in
        (Syntax.Refl (t', e'), loc)

    | Syntax.J (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
      let t' = ty t in
        begin match term e2 with

          (* norm-j-redex *)
          | (Syntax.Idpath (t'', e2'), _)
               when Syntax.equal_ty t' t'' ->
             let e1' = term e1 in
               term (Syntax.beta e1' e2')
                 
          (* norm-j-other *)
          | e2' ->
            let u' = ty u in
            let e1' = term e1 in
            let e3' = term e3 in
            let e4' = term e4 in
              (Syntax.J (t', (x, y, p, u'), (z, e1'), e2', e3', e4'), loc)
        end

    | Syntax.Coerce (alpha, beta, e) ->
      begin match term e with

        (* norm-coerce-trivial *)
        | e' when Universe.eq alpha beta -> e'

        (* norm-coerce-trans *)
        | (Syntax.Coerce (gamma, delta, e'), loc)
            when Universe.eq alpha delta ->
          term (Syntax.Coerce (gamma, beta, e'), loc)

        (* norm-coerce-pi *)
        | (Syntax.NameProd (gamma, delta, x, e1, e2), loc)
            when Universe.eq alpha (Universe.max gamma delta) &&
                 Universe.leq gamma alpha && Universe.leq delta alpha ->
          let e1' = term (Syntax.Coerce (gamma, beta, e1), snd e1) in
          let e2' = term (Syntax.Coerce (delta, beta, e2), snd e2) in
            (Syntax.NameProd (beta, beta, x, e1', e2'), loc)

        (* norm-coerce-paths *)
        | (Syntax.NamePaths (gamma, e1, e2, e3), loc)
            when Universe.eq alpha gamma ->
          let e1' = term (Syntax.Coerce (alpha, beta, e1), snd e1) in
          let e2' = term e2 in
          let e3' = term e3 in
            (Syntax.NamePaths (beta, e1', e2', e3'), loc)

        (* norm-coerce-id *)
        | (Syntax.NameId (gamma, e1, e2, e3), loc)
            when Universe.eq alpha gamma ->
          let e1' = term (Syntax.Coerce (alpha, beta, e1), snd e1) in
          let e2' = term e2 in
          let e3' = term e3 in
            (Syntax.NameId (beta, e1', e2', e3'), loc)

        (* name-coerce-other *)
        | e' ->
          (Syntax.Coerce (alpha, beta, e'), loc)
      end

    (* norm-name-unit *)
    | Syntax.NameUnit -> e    

    (* norm-name-prod *)
    | Syntax.NameProd (alpha, beta, x, e1, e2) ->
      let e1' = term e1 in
      let e2' = term e2 in
        (Syntax.NameProd (alpha, beta, x, e1', e2'), loc)

    (* norm-name-universe *)
    | Syntax.NameUniverse _ -> e

    (* norm-name-paths *)
    | Syntax.NamePaths (alpha, e1, e2, e3) ->
      let e1' = term e1 in
      let e2' = term e2 in
      let e3' = term e3 in
        (Syntax.NamePaths (alpha, e1', e2', e3'), loc)

    (* norm-name-id *)
    | Syntax.NameId (alpha, e1, e2, e3) ->
      let e1' = term e1 in
      let e2' = term e2 in
      let e3' = term e3 in
        (Syntax.NameId (alpha, e1', e2', e3'), loc)
