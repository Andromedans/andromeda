(** Simplification of expressions and types. *)

let is_small {Tt.term=e';_} =
match e' with
  | Tt.Constant (_, es) -> es = []
  | Tt.Type | Tt.Bound _ | Tt.Atom _ -> true
  | Tt.Lambda _ | Tt.Spine _ | Tt.Prod _ | Tt.Refl _ | Tt.Eq _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ -> false

let rec term ({Tt.term=e';loc;_} as e) =
    match e' with

    | Tt.Type -> e

    | Tt.Atom _ -> e

    | Tt.Lambda ((x,u), (e,t)) ->
      let u = ty u in
      let y = Name.fresh x in
      let e = Tt.unabstract [y] e
      and t = Tt.unabstract_ty [y] t in
      let e = term e
      and t = ty t in
      let e = Tt.abstract [y] e
      and t = Tt.abstract_ty [y] t in
      Tt.mk_lambda ~loc x u e t

    | Tt.Constant(x, es) ->
      let es = List.map (term) es in
        Tt.mk_constant ~loc x es

    | Tt.Spine (e1, ((x, a),b), e2) ->
      spine ~loc e1 x a b e2

    | Tt.Prod ((x,u), t) ->
      let u = ty u in
      let y = Name.fresh x in
      let t = Tt.unabstract_ty [y] t in
      let t = ty t in
      let t = Tt.abstract_ty [y] t in
      Tt.mk_prod ~loc x u t

    | Tt.Eq (t, e1, e2) ->
      let t = ty t
      and e1 = term e1
      and e2 = term e2 in
        Tt.mk_eq ~loc t e1 e2

    | Tt.Refl (t, e) ->
      let t = ty t
      and e = term e in
        Tt.mk_refl ~loc t e

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
      Error.impossible ~loc "de Bruijn encountered in term"

and ty (Tt.Ty e) =
  let e = term e in
    Tt.ty e

and spine ~loc h x a b e =

  (* First we simplify the head and the arguments. *)
  let {Tt.term=h';_} as h = term h
  and e = term e
  and a = ty a
  and y = Name.fresh x in
  let b = Tt.unabstract_ty [y] b in
  let b = ty b in
  let b = Tt.abstract_ty [y] b in
  
  (* Then we check whether we have a beta redex: *)
  match h' with

  | Tt.Lambda ((y,u), (d, v)) when
      (* Do the types match? *)
      (let t1 = Tt.mk_prod_ty ~loc y u v
       and t2 = Tt.mk_prod_ty ~loc x a b in
        Tt.alpha_equal_ty t1 t2)
    ->
    begin
      if is_small e || (Tt.occurs_term_ty 0 (d,v) <= 1)
      then
        let d = Tt.instantiate [e] d in
        term d
      else
        let h = Tt.mk_lambda ~loc:(h.Tt.loc) y u d v in
        Tt.mk_spine ~loc h x a b e
    end

  (* All the cases where a reduction is not possible. *)
  | Tt.Constant _
  | Tt.Lambda _
  | Tt.Spine _
  | Tt.Atom _
  | Tt.Type
  | Tt.Prod _
  | Tt.Eq _
  | Tt.Refl _
  | Tt.Signature _
  | Tt.Structure _ 
  | Tt.Projection _ ->
    Tt.mk_spine ~loc h x a b e

  | Tt.Bound _ ->
    Error.impossible ~loc "de Bruijn encountered in Simplify.spine"

and project ~loc te xts p =
  match te.Tt.term with
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
  | Tt.Prod _
  | Tt.Eq _
  | Tt.Refl _
  | Tt.Signature _
  | Tt.Projection _ -> Tt.mk_projection ~loc te xts p
                                        
  | Tt.Bound _ ->
     Error.impossible ~loc "de Bruijn encountered in Simplify.project"

let context ctx = ctx

let rec value = function
  | Value.Term (ctx,e,t) -> Value.mk_term (Judgement.mk_term (context ctx) (term e) (ty t))
  | Value.Ty (ctx,t) -> Value.mk_ty (Judgement.mk_ty (context ctx) (ty t))
  | Value.Tag (x,vs) -> Value.mk_tag x (List.map value vs)
  | Value.List lst ->
    let lst = List.map value lst in
    Value.from_list lst
  | Value.Ref _ | Value.Closure _ | Value.Handler _ | Value.String _ as v -> v

