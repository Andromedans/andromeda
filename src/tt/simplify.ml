(** Simplification of expressions and types. *)

let is_small (e',_) =
match e' with
  | Tt.Type | Tt.Bound _ | Tt.Name _ -> true
  | Tt.Lambda _ | Tt.Spine _ | Tt.Prod _ | Tt.Refl _ | Tt.Eq _ -> false

let rec simplify ctx ((e',loc) as e) =
    match e' with

    | Tt.Type -> e

    | Tt.Name _ -> e

    | Tt.Lambda (xts, (e,t)) ->
      let rec fold ctx ys xts = function
        | [] ->
          let e = Tt.unabstract ys 0 e in
          let e = simplify ctx e in
          let e = Tt.abstract ys 0 e in
          let t = Tt.unabstract_ty ys 0 t in
          let t = simplify_ty ctx t in
          let t = Tt.abstract_ty ys 0 t in
            Tt.mk_lambda ~loc xts e t
        | (x,u) :: xus ->
          let u = Tt.unabstract_ty ys 0 u in
          let u = simplify_ty ctx u in
          let y, ctx = Context.add_fresh x u ctx in
          let u = Tt.abstract_ty ys 0 u in
            fold ctx (y::ys) (xts @ [(x,u)]) xus
      in
        fold ctx [] [] xts

    | Tt.Spine (e, (xets, t)) ->
      simplify_spine ~loc ctx e xets t

    | Tt.Prod (xts, t) ->
      let rec fold ctx ys xts = function
        | [] ->
          let t = Tt.unabstract_ty ys 0 t in
          let t = simplify_ty ctx t in
          let t = Tt.abstract_ty ys 0 t in
            Tt.mk_prod ~loc xts t
        | (x,u) :: xus ->
          let u = Tt.unabstract_ty ys 0 u in
          let u = simplify_ty ctx u in
          let y, ctx = Context.add_fresh x u ctx in
          let u = Tt.abstract_ty ys 0 u in
            fold ctx (y::ys) (xts @ [(x,u)]) xus
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

    | Tt.Bound _ ->
      Error.impossible "de Bruijn encountered in simplify"

and simplify_ty ctx (Tt.Ty e) =
  let e = simplify ctx e in
    Tt.ty e

and simplify_spine ~loc ctx h xets t =

  (* Auxiliary function for simplifying the spine arguments *)
  let rec simplify_xetst ctx ys xeus = function
  | [] ->
    let t = Tt.unabstract_ty ys 0 t in
    let t = simplify_ty ctx t in
    let t = Tt.abstract_ty ys 0 t in
      xeus, t
  | (x, (e,u)) :: xets ->
    let e = Tt.unabstract ys 0 e in
    let e = simplify ctx e in
    let u = Tt.unabstract_ty ys 0 u in
    let u = simplify_ty ctx u in
    let y, ctx = Context.add_fresh x u ctx in
    let e = Tt.abstract ys 0 e
    and u = Tt.abstract_ty ys 0 u in
      simplify_xetst ctx (y::ys) (xeus @ [(x,(e,u))]) xets
  in

  (* First we simplify the head and the arguments. *)
  let (h',eloc) as h = simplify ctx h
  and xets, t = simplify_xetst ctx [] [] xets in

  (* Then we check whether we have a beta redex: *)
  match h' with

  | Tt.Lambda (xus, (e, u)) when
      (* Do the types match? *)
      (let t1 = Tt.mk_prod_ty ~loc xus u
       and t2 = Tt.mk_prod_ty ~loc (List.map (fun (x,(_,t)) -> (x,t)) xets) t in
        Equal.alpha_equal_ty t1 t2)
    ->
    begin
      let rec reduce xus eu xets =
        match xus, xets with
        | (x,u)::xus, (_,(e',t))::xets when
            is_small e' ||
            Tt.occurs_abstraction Tt.occurs_ty Tt.occurs_term_ty 0 (xus, eu) <= 1
          ->
            let xus, eu =
              Tt.instantiate_abstraction
                Tt.instantiate_ty Tt.instantiate_term_ty
                [e'] 0 (xus, eu)
            in
              reduce xus eu xets
        | _ -> Tt.mk_spine ~loc (Tt.mk_lambda ~loc xus (fst eu) (snd eu)) xets t
      in
      reduce xus (e,u) xets
    end

  (* All the cases where a reduction is not possible. *)
  | Tt.Lambda _
  | Tt.Spine _
  | Tt.Name _
  | Tt.Type
  | Tt.Prod _
  | Tt.Eq _
  | Tt.Refl _ ->
    Tt.mk_spine ~loc h xets t

  | Tt.Bound _ ->
    Error.impossible ~loc "de Bruijn encountered in simplify_spine"
