(** Simplification of expressions and types. *)

let is_small (e',_) =
match e' with
  | Tt.PrimApp (_, es) -> es = []
  | Tt.Type | Tt.Inhab | Tt.Bound _ | Tt.Name _ | Tt.Atom _ -> true
  | Tt.Lambda _ | Tt.Spine _ | Tt.Prod _ | Tt.Refl _ | Tt.Eq _ | Tt.Bracket _ -> false

let rec simplify ctx ((e',loc) as e) =
    match e' with

    | Tt.Type -> e

    | Tt.Inhab -> e

    | Tt.Name _ -> e

    | Tt.Atom _ -> e

    | Tt.Lambda (xts, (e,t)) ->
      let rec fold ctx ys xts = function
        | [] ->
          let e = Tt.unabstract ys 0 e in
          let e = simplify ctx e in
          let e = Tt.abstract ys 0 e in
          let t = Tt.unabstract_ty ys 0 t in
          let t = simplify_ty ctx t in
          let t = Tt.abstract_ty ys 0 t in
            Tt.mk_lambda ~loc (List.rev xts) e t
        | (x,u) :: xus ->
          let u = Tt.unabstract_ty ys 0 u in
          let u = simplify_ty ctx u in
          let y, ctx = Context.add_fresh ~loc ctx x u in
          let u = Tt.abstract_ty ys 0 u in
            fold ctx (y::ys) ((x,u) :: xts) xus
      in
        fold ctx [] [] xts

    | Tt.PrimApp(x, es) ->
      let es = List.map (simplify ctx) es in
        Tt.mk_primapp ~loc x es

    | Tt.Spine (e, (xts, t), es) ->
      simplify_spine ~loc ctx e xts t es

    | Tt.Prod (xts, t) ->
      let rec fold ctx ys xts = function
        | [] ->
          let t = Tt.unabstract_ty ys 0 t in
          let t = simplify_ty ctx t in
          let t = Tt.abstract_ty ys 0 t in
            Tt.mk_prod ~loc (List.rev xts) t
        | (x,u) :: xus ->
          let u = Tt.unabstract_ty ys 0 u in
          let u = simplify_ty ctx u in
          let y, ctx = Context.add_fresh ctx ~loc x u
          and u = Tt.abstract_ty ys 0 u in
            fold ctx (y::ys) ((x,u) :: xts) xus
      in
        fold ctx [] [] xts

    | Tt.Eq (t, e1, e2) ->
      let t = simplify_ty ctx t
      and e1 = simplify ctx e1
      and e2 = simplify ctx e2 in
        Tt.mk_eq ~loc t e1 e2

    | Tt.Refl (t, e) ->
      let t = simplify_ty ctx t
      and e = simplify ctx e in
        Tt.mk_refl ~loc t e

    | Tt.Bracket t ->
      let t = simplify_ty ctx t in
        Tt.mk_bracket ~loc t

    | Tt.Bound _ ->
      Error.impossible "de Bruijn encountered in simplify"

and simplify_ty ctx (Tt.Ty e) =
  let e = simplify ctx e in
    Tt.ty e

and simplify_spine ~loc ctx h xts t es =

  (* Auxiliary function for simplifying the spine arguments *)
  let rec simplify_xts ctx ys xus = function
  | [] ->
    let t = Tt.unabstract_ty ys 0 t in
    let t = simplify_ty ctx t in
    let t = Tt.abstract_ty ys 0 t in
      List.rev xus, t
  | (x, u) :: xts ->
    let u = Tt.unabstract_ty ys 0 u in
    let u = simplify_ty ctx u in
    let y, ctx = Context.add_fresh ~loc ctx x u
    and u = Tt.abstract_ty ys 0 u in
      simplify_xts ctx (y::ys) ((x,u) :: xus) xts
  in

  (* First we simplify the head and the arguments. *)
  let (h', _) as h = simplify ctx h
  and xts, t = simplify_xts ctx [] [] xts
  and es = List.map (simplify ctx) es in

  (* Then we check whether we have a beta redex: *)
  match h' with

  | Tt.Lambda (yus, (d, u)) when
      (* Do the types match? *)
      (let t1 = Tt.mk_prod_ty ~loc yus u
       and t2 = Tt.mk_prod_ty ~loc xts t in
        Equal.alpha_equal_ty t1 t2)
    ->
    begin
      let rec reduce yus du xts es =
        match yus, xts, es with
        | (y,u)::yus, (_,t)::xts, e::es when
            is_small e ||
            Tt.occurs_abstraction Tt.occurs_ty Tt.occurs_term_ty 0 (yus, du) <= 1
          ->
            let yus, du =
              Tt.instantiate_abstraction
                Tt.instantiate_ty Tt.instantiate_term_ty
                [e] 0 (yus, du)
            in
              reduce yus du xts es
        | _ -> Tt.mk_spine ~loc (Tt.mk_lambda ~loc yus (fst du) (snd du)) xts t es
      in
      reduce yus (d,u) xts es
    end

  (* All the cases where a reduction is not possible. *)
  | Tt.PrimApp _
  | Tt.Lambda _
  | Tt.Spine _
  | Tt.Name _
  | Tt.Atom _
  | Tt.Type
  | Tt.Inhab
  | Tt.Bracket _
  | Tt.Prod _
  | Tt.Eq _
  | Tt.Refl _ ->
    Tt.mk_spine ~loc h xts t es

  | Tt.Bound _ ->
    Error.impossible ~loc "de Bruijn encountered in simplify_spine"
