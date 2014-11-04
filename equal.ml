let rec equal_ty ctx t1 t2 = equal ctx t1 t2 Syntax.typ

and equal ctx ((_,loc1) as e1) ((_,loc2) as e2) t =
  Syntax.equal e1 e2 ||
    (* xxx should check equations here *)
    begin (* type-directed phase *)
      let ((t',_) as t) = whnf_ty ctx t
      match t' with

        | Syntax.Type ->
        | Syntax.Name _ -> 
        | Syntax.App _ ->
        | Syntax.Ascribe _ ->
          equal_whnf ctx e1 e2 t

        | Syntax.Prod (x, t1, t2) ->
          let y, ctx = Context.add_fresh x t1 in
          let y = Syntax.mk_name ~loc:Position.Nowhere y in
          let t2 = Syntax.instantiate_ty y t2
          and e1' = Syntax.mk_app ~loc:loc1 x t1 t2 e1 y
          and e2' = Syntax.mk_app ~loc:loc2 x t1 t2 e2 y
          in equal ctx e1' e2' t2

        | Syntax.Eq _ -> true (** Strict equality *)

        | Syntax.Bound _ -> Error.impossible ~loc:loc1 "de Bruijn encountered in equal"

        | Syntax.Lambda _ -> Error.impossible ~loc:loc1 "fun is not a type"

        | Syntax.Refl _ -> Error.impossible ~loc:loc1 "refl is not a type"
    end
    
and equal_whnf ctx e1 e2 ((_,loc) as t) =
  let (e1',loc1) as e1 = whnf ctx e1 t
  and (e2',loc2) as e2 = whnf ctx e2 t
  in
    Syntax.equal e1 e2 ||
    begin match e1', e2' with

      | Name x, Name y -> x = y

      | Bound _, _ | _, Bound _ ->
        Error.impossible ~loc:loc1 "de Bruijn encountered in equal_whnf"

      | Ascribe (e,u), Ascribe (e',u') ->
        Error.impossible ~loc:loc1 "ascription is not a weak head-normal form"

      | Lambda (x, u1, u2, e), Lambda (_, u1', u2', e') ->
        equal_ty ctx u1 u1'
        &&
        begin
          let y, ctx = Context.add_fresh x u1 in
          let u2  = Syntax.instantiate_ty y u2
          and u2' = Syntax.instantiate_ty y u2'
          and e  = Syntax.instantiate y e
          and e' = Syntax.instantiate y e'
          in
            equal_ty ctx u2 u2' &&
            equal ctx e e' u2
        end
       
      | App ((x,u1,u2), d1, d2), App ((_,u1',u2'), d1', d2') ->
        equal_ty ctx u1 u1'
        &&
        begin
          let y, ctx = Context.add_fresh x u1 in
          let u2  = Syntax.instantiate y u2
          and u2' = Syntax.instantiate y u2'
          in
            equal_ty ctx u2 u2'
        end 
        &&
        begin
          let u' = Syntax.mk_prod ~loc:loc x u1 u2
          in equal ctx d1 d1' u'
        end
        &&
        equal ctx d2 d2' u1
        
      | Type, Type -> true

      | Prod (x, u1, u2), Prod (_, u1', u2') ->
        equal_ty ctx u1 u1' &&
        begin 
          let y, ctx = Context.add_fresh x u1 in
          let u2  = Syntax.instantiate y u2
          and u2' = Syntax.instantiate y u2'
          in
            equal_ty ctx u2 u2'
        end

      | Eq (u, d1, d2), Eq (u', d1', d2') ->
        equal_ty ctx u u' &&
        equal ctx d1 d1' u &&
        equal ctx d2 d2' u

      | Refl (u, d), Refl (u', d') ->
        equal_ty ctx u u' &&
        equal ctx d d' u

      | (Name _ | | Ascribe _ | Lambda _ | App _ | Type | Prod _ | Eq _ | Refl _) | _ ->
        false

    end
