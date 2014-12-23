(** The whnf of a type [t] in context [ctx]. *)
let rec whnf_ty ctx t =
  whnf ctx t Syntax.typ

(** The whnf of term [e] at type [t] in context [ctx]. *)
and whnf ctx ((e',loc) as e) t =
  match e' with

    | Syntax.Name _ -> e

    | Syntax.Bound _ -> Error.impossible ~loc "deBruijn encountered in whnf"

    | Syntax.Ascribe (e, u) -> whnf ctx e u (* xxx is this correct? *)

    | Syntax.Lambda _ -> e

    | Syntax.Spine (t, e1, e2::es) ->
      whnf_spine ~loc ctx t e1 e2 es

    | Syntax.Spine (_, _, []) ->
      Error.impossible ~loc "empty spine in whnf"
      
    | Syntax.Type -> e

    | Syntax.Prod _ -> e

    | Syntax.Eq _ -> e

    | Syntax.Refl _ -> e

(** The whnf of a spine [e1 e2 ... es ...] at type [t] in context [ctx]. *)
and whnf_spine ~loc ctx ((t',loc) as t) e1 e2 es =
  let rec spine_cod ((t',loc) as t) es =
    begin match t', es with
      | _, [] -> t
      | Syntax.Prod (_, t1, t2), e::es ->
        let t = Syntax.instantiate_ty e t2 in
          spine_cod t es
      | _, _ -> Error.impossible ~loc "malformed spine type in whnf_spine, spine_cod"
    end
  in
  match t' with
    | Syntax.Prod (x,t1,t2) ->
      let (e1',_) as e1 = whnf ctx e1 t in
        begin match e1' with
            
          | Syntax.Spine (t', e', es') when
              (let u = spine_cod t' es in equal_ty ctx u t) ->
            begin match es' @ (e2 :: es) with
              | e2 :: es -> whnf_spine ~loc ctx t' e' e2 es
              | [] -> assert false
            end
              
          | Syntax.Lambda (_, u1, u2, e') when equal_as_prod ctx x t1 t2 u1 u2 ->
            let e1 = Syntax.instantiate e2 e'
            and t = Syntax.instantiate_ty e2 t2
            in begin match es with
              | [] -> whnf ctx e1 t
              | e2::es -> whnf_spine ~loc ctx t e1 e2 es
            end
              
          | (Syntax.Name _ | Syntax.Bound _ | Syntax.Ascribe _ | Syntax.Type |
              Syntax.Prod _ | Syntax.Eq _ | Syntax.Refl _ | Syntax.Spine _ | Syntax.Lambda _ ) ->
            Syntax.mk_spine ~loc t e1 (e2::es)

        end

    | _ -> Error.impossible ~loc "malformed spine type in whnf_spine"

and equal_ty ctx t1 t2 = equal ctx t1 t2 Syntax.typ

and equal_as_prod ctx x t1 t2 u1 u2 =
  equal_ty ctx t1 u1 &&
  begin
    let y, ctx = Context.add_free x t1 ctx in
    let y' = Syntax.mk_name ~loc:Position.nowhere y in
    let t2 = Syntax.instantiate_ty y' t2
    and u2 = Syntax.instantiate_ty y' u2
    in equal_ty ctx t2 u2
  end

and equal ctx ((_,loc1) as e1) ((_,loc2) as e2) t =
  Syntax.equal e1 e2 ||
    (* xxx should check equations here *)
    begin (* type-directed phase *)
      let ((t',_) as t) = whnf_ty ctx t in
      match t' with

        | Syntax.Type
        | Syntax.Name _
        | Syntax.Spine _
        | Syntax.Ascribe _ ->
          equal_whnf ctx e1 e2 t

        | Syntax.Prod (x, t1, t2) ->
          let y, ctx = Context.add_free x t1 ctx in
          let y = Syntax.mk_name ~loc:Position.nowhere y in
          let t2 = Syntax.instantiate_ty y t2
          and e1' = Syntax.mk_app ~loc:loc1 x t1 t2 e1 y
          and e2' = Syntax.mk_app ~loc:loc2 x t1 t2 e2 y
          in equal ctx e1' e2' t2

        | Syntax.Eq _ -> true (** Strict equality *)

        | Syntax.Bound _ -> Error.impossible ~loc:loc1 "deBruijn encountered in equal"

        | Syntax.Lambda _ -> Error.impossible ~loc:loc1 "fun is not a type"

        | Syntax.Refl _ -> Error.impossible ~loc:loc1 "refl is not a type"
    end
    
and equal_whnf ctx e1 e2 ((_,loc) as t) =
  let (e1',loc1) as e1 = whnf ctx e1 t
  and (e2',loc2) as e2 = whnf ctx e2 t
  in
    Syntax.equal e1 e2 ||
    begin match e1', e2' with

      | Syntax.Name x, Syntax.Name y -> x = y

      | Syntax.Bound _, _ | _, Syntax.Bound _ ->
        Error.impossible ~loc:loc1 "deBruijn encountered in equal_whnf"

      | Syntax.Ascribe (e,u), Syntax.Ascribe (e',u') ->
        Error.impossible ~loc:loc1 "ascription is not a weak head-normal form"

      | Syntax.Lambda (x, u1, u2, e), Syntax.Lambda (_, u1', u2', e') ->
        equal_ty ctx u1 u1'
        &&
        begin
          let y, ctx = Context.add_free x u1 ctx in
          let y' = Syntax.mk_name ~loc:Position.nowhere y in
          let u2  = Syntax.instantiate_ty y' u2
          and u2' = Syntax.instantiate_ty y' u2'
          and e  = Syntax.instantiate y' e
          and e' = Syntax.instantiate y' e'
          in
            equal_ty ctx u2 u2' &&
            equal ctx e e' u2
        end
       
      | Syntax.Spine (t, e, es), Syntax.Spine (t', e', es') ->
          List.length es = List.length es'
          &&
          equal_ty ctx t t'
          &&
          equal ctx e e' t
          &&
          equal_args ctx t es es'

      | Syntax.Type, Syntax.Type -> true

      | Syntax.Prod (x, u1, u2), Syntax.Prod (_, u1', u2') ->
        equal_ty ctx u1 u1' &&
        begin 
          let y, ctx = Context.add_free x u1 ctx in
          let y' = Syntax.mk_name ~loc:Position.nowhere y in
          let u2  = Syntax.instantiate_ty y' u2
          and u2' = Syntax.instantiate_ty y' u2'
          in
            equal_ty ctx u2 u2'
        end

      | Syntax.Eq (u, d1, d2), Syntax.Eq (u', d1', d2') ->
        equal_ty ctx u u' &&
        equal ctx d1 d1' u &&
        equal ctx d2 d2' u

      | Syntax.Refl (u, d), Syntax.Refl (u', d') ->
        equal_ty ctx u u' &&
        equal ctx d d' u

      | (Syntax.Name _ | Syntax.Ascribe _ | Syntax.Lambda _ | Syntax.Spine _ |
          Syntax.Type | Syntax.Prod _ | Syntax.Eq _ | Syntax.Refl _), _ ->
        false

    end

and equal_args ctx (t',loc) es es' =
  begin match es, es' with
    | [], [] -> Error.impossible ~loc "comparing empty lists of argumanets in equal_args"
    | [e], [e'] -> 
      begin match t' with
        | Syntax.Prod (_,t1,t2) -> equal ctx e e' t1
        | _ -> Error.impossible ~loc "malformed spine type in equal_args (1)"
      end
    | e::es, e'::es' ->
      begin match t' with
          (* we do not have to call as_prod here as a spine type must be a [Prod] *)
        | Syntax.Prod (_,t1,t2) ->
          equal ctx e e' t1 &&
            begin
              let t = Syntax.instantiate_ty e t2
              in equal_args ctx t es es'
            end
        | _ -> Error.impossible ~loc "malformed spine type in equal_args (2)"
      end
    | [],_::_ | _::_,[] -> false
  end

and as_prod ctx t =
  let (t',_) = whnf_ty ctx t in
    match t' with
      | Syntax.Prod (x, t1, t2) -> (x, t1, t2)
      | _ ->
        Error.typing "product expected but found %t"
          (Print.ty ctx t)
