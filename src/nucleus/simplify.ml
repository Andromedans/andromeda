(** Simplification of expressions and types. *)

let is_small (e',_) =
match e' with
  | Tt.Constant (_, es) -> es = []
  | Tt.Type | Tt.Inhab _ | Tt.Bound _ | Tt.Atom _ -> true
  | Tt.Lambda _ | Tt.Spine _ | Tt.Prod _ | Tt.Refl _ | Tt.Eq _
  | Tt.Bracket _ | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ -> false

let rec term ((e',loc) as e) =
    match e' with

    | Tt.Type -> e

    | Tt.Inhab t ->
       let t = ty t in
       Tt.mk_inhab ~loc t

    | Tt.Atom _ -> e

    | Tt.Lambda (xts, (e,t)) ->
      let rec fold ys xts = function
        | [] ->
          let e = Tt.unabstract ys e in
          let e = term e in
          let e = Tt.abstract ys e in
          let t = Tt.unabstract_ty ys t in
          let t = ty t in
          let t = Tt.abstract_ty ys t in
            Tt.mk_lambda ~loc (List.rev xts) e t
        | (x,u) :: xus ->
          let u = Tt.unabstract_ty ys u in
          let u = ty u in
          let u = Tt.abstract_ty ys u in
          let y = Name.fresh x in
            fold (y::ys) ((x,u) :: xts) xus
      in
        fold [] [] xts

    | Tt.Constant(x, es) ->
      let es = List.map (term) es in
        Tt.mk_constant ~loc x es

    | Tt.Spine (e, (xts, t), es) ->
      spine ~loc e xts t es

    | Tt.Prod (xts, t) ->
      let rec fold ys xts = function
        | [] ->
          let t = Tt.unabstract_ty ys t in
          let t = ty t in
          let t = Tt.abstract_ty ys t in
            Tt.mk_prod ~loc (List.rev xts) t
        | (x,u) :: xus ->
          let u = Tt.unabstract_ty ys u in
          let u = ty u in
          let u = Tt.abstract_ty ys u in
          let y = Name.fresh x in
            fold (y::ys) ((x,u) :: xts) xus
      in
        fold [] [] xts

    | Tt.Eq (t, e1, e2) ->
      let t = ty t
      and e1 = term e1
      and e2 = term e2 in
        Tt.mk_eq ~loc t e1 e2

    | Tt.Refl (t, e) ->
      let t = ty t
      and e = term e in
        Tt.mk_refl ~loc t e

    | Tt.Bracket t ->
      let t = ty t in
        Tt.mk_bracket ~loc t

    | Tt.Signature xts ->
      let rec fold ys res = function
        | [] -> List.rev res
        | (x,y,t)::rem ->
          let t = Tt.unabstract_ty ys t in
          let t = ty t in
          let t = Tt.abstract_ty ys t in
          let y' = Name.fresh y in
          fold (y'::ys) ((x,y,t)::res) rem
        in
      let xts = fold [] [] xts in
      Tt.mk_signature ~loc xts

    | Tt.Structure xts ->
      let rec fold ys res = function
        | [] -> List.rev res
        | (x,y,t,te)::rem ->
          let t = Tt.unabstract_ty ys t in
          let t = ty t in
          let t = Tt.abstract_ty ys t in
          let te = Tt.unabstract ys te in
          let te = term te in
          let te = Tt.abstract ys te in
          let y' = Name.fresh y in
          fold (y'::ys) ((x,y,t,te)::res) rem
        in
      let xts = fold [] [] xts in
      Tt.mk_structure ~loc xts

    | Tt.Projection (te, xts, p) ->
      let te = term te in
      let rec fold ys res = function
        | [] -> List.rev res
        | (x,y,t)::rem ->
          let t = Tt.unabstract_ty ys t in
          let t = ty t in
          let t = Tt.abstract_ty ys t in
          let y' = Name.fresh y in
          fold (y'::ys) ((x,y,t)::res) rem
        in
      let xts = fold [] [] xts in
      project ~loc te xts p

    | Tt.Bound _ ->
      Error.impossible "de Bruijn encountered in term"

and ty (Tt.Ty e) =
  let e = term e in
    Tt.ty e

and spine ~loc h xts t es =

  (* Auxiliary function for simplifying the spine arguments *)
  let rec simplify_xts ys xus = function
  | [] ->
    let t = Tt.unabstract_ty ys t in
    let t = ty t in
    let t = Tt.abstract_ty ys t in
      List.rev xus, t
  | (x, u) :: xts ->
    let u = Tt.unabstract_ty ys u in
    let u = ty u in
    let u = Tt.abstract_ty ys u
    and y = Name.fresh x in
      simplify_xts (y::ys) ((x,u) :: xus) xts
  in

  (* First we simplify the head and the arguments. *)
  let (h', _) as h = term h
  and xts, t = simplify_xts [] [] xts
  and es = List.map term es in

  (* Then we check whether we have a beta redex: *)
  match h' with

  | Tt.Lambda (yus, (d, u)) when
      (* Do the types match? *)
      (let t1 = Tt.mk_prod_ty ~loc yus u
       and t2 = Tt.mk_prod_ty ~loc xts t in
        Tt.alpha_equal_ty t1 t2)
    ->
    begin
      let rec reduce yus du xts es =
        match yus, xts, es with
        | (y,u)::yus, (_,t)::xts, e::es when
            is_small e ||
            Tt.occurs_ty_abstraction Tt.occurs_term_ty 0 (yus, du) <= 1
          ->
            let yus, du =
              Tt.instantiate_ty_abstraction Tt.instantiate_term_ty [e] (yus, du)
            in
              reduce yus du xts es
        | _ -> Tt.mk_spine ~loc (Tt.mk_lambda ~loc yus (fst du) (snd du)) xts t es
      in
      reduce yus (d,u) xts es
    end

  (* All the cases where a reduction is not possible. *)
  | Tt.Constant _
  | Tt.Lambda _
  | Tt.Spine _
  | Tt.Atom _
  | Tt.Type
  | Tt.Inhab _
  | Tt.Bracket _
  | Tt.Prod _
  | Tt.Eq _
  | Tt.Refl _
  | Tt.Signature _
  | Tt.Structure _ 
  | Tt.Projection _ ->
    Tt.mk_spine ~loc h xts t es

  | Tt.Bound _ ->
    Error.impossible ~loc "de Bruijn encountered in Simplify.spine"

and project ~loc te xts p =
  let te',_ = te in match te' with
    | Tt.Structure xtes ->
      let sig1 = Tt.mk_signature ~loc (List.map (fun (x,y,t,_) -> x,y,t) xtes) in
      let sig2 = Tt.mk_signature ~loc xts in
      if Tt.alpha_equal sig1 sig2
      then
        let te = Tt.field_value ~loc xtes p in
        term te
      else Tt.mk_projection ~loc te xts p
    | Tt.Constant _
    | Tt.Lambda _
    | Tt.Spine _
    | Tt.Atom _
    | Tt.Type
    | Tt.Inhab _
    | Tt.Bracket _
    | Tt.Prod _
    | Tt.Eq _
    | Tt.Refl _
    | Tt.Signature _
    | Tt.Projection _ -> Tt.mk_projection ~loc te xts p
    
    | Tt.Bound _ ->
      Error.impossible ~loc "de Bruijn encountered in Simplify.project"

let context ctx = ctx

