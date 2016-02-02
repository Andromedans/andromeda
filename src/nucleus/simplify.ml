(** Simplification of expressions and types. *)

let is_small {Tt.term=e';_} =
match e' with
  | Tt.Type | Tt.Bound _ | Tt.Constant _ | Tt.Atom _ -> true
  | Tt.Lambda _ | Tt.Apply _ | Tt.Prod _ | Tt.Refl _ | Tt.Eq _
  | Tt.Signature _ | Tt.Structure _ | Tt.Projection _ -> false

let rec term ({Tt.term=e';loc;_} as e) =
    match e' with

    | Tt.Type -> e

    | Tt.Atom _ -> e

    | Tt.Constant _ -> e

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

    | Tt.Apply (e1, ((x, a),b), e2) ->
      apply ~loc e1 x a b e2

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

    | Tt.Signature _ -> e

    | Tt.Structure (s, es) ->
       let es = List.map term es in
       Tt.mk_structure ~loc s es

    | Tt.Projection (e, s, l) ->
       let e = term e in
       (* TODO pass in the environment and properly reduce here *)
       Tt.mk_projection ~loc e s l

    | Tt.Bound _ ->
      Error.impossible ~loc "de Bruijn encountered in term"

and ty (Tt.Ty e) =
  let e = term e in
    Tt.ty e

and apply ~loc h x a b e =

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
        Tt.mk_apply ~loc h x a b e
    end

  (* All the cases where a reduction is not possible. *)
  | Tt.Constant _
  | Tt.Lambda _
  | Tt.Apply _
  | Tt.Atom _
  | Tt.Type
  | Tt.Prod _
  | Tt.Eq _
  | Tt.Refl _
  | Tt.Signature _
  | Tt.Structure _
  | Tt.Projection _ ->
    Tt.mk_apply ~loc h x a b e
  | Tt.Bound _ ->
    Error.impossible ~loc "de Bruijn encountered in Simplify.apply"

let context ctx = ctx

let rec value = function
  | Value.Term (Jdg.Term (ctx,e,t)) -> Value.mk_term (Jdg.mk_term (context ctx) (term e) (ty t))
  | Value.Tag (x,vs) -> Value.mk_tag x (List.map value vs)
  | Value.List lst -> Value.from_list (List.map value lst)
  | Value.Tuple lst -> Value.mk_tuple (List.map value lst)
  | Value.Ref _ | Value.Closure _ | Value.Handler _ | Value.String _ as v -> v

