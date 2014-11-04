let rec whnf_ty ctx t =
  whnf ctx t Syntax.typ

and whnf ctx ((e',loc) as e) t =
  Print.debug "whnf: %t :: %t"
    (Print.term ctx e) (Print.term ctx t) ;
  match e' with

    | Syntax.Name _ -> e

    | Syntax.Bound _ -> Error.impossible ~loc "deBruijn encountered in whnf"

    | Syntax.Ascribe (e, u) -> whnf ctx e u (* xxx is this correct? *)

    | Syntax.Lambda _ -> e

    | Syntax.App ((x, u1, u2), e1, e2) ->
      (* xxx should check that t2 e1 matches t? *)
      begin
          let e1 = whnf ctx e1 (Syntax.mk_prod ~loc x u1 u2) in
            match fst e1 with
              (* norm-app-beta *)
              | Syntax.Lambda (_, t1, t2, e1') when
                equal_ty ctx u1 t1 &&
                (let x, ctx = Context.add_fresh x u1 ctx in
                 let x' = Syntax.mk_name ~loc:Position.Nowhere x in
                 let u2 = Syntax.instantiate_ty x' u2
                 and t2 = Syntax.instantiate_ty x' t2 in
                   equal_ty ctx u2 t2) ->
                let e1' = Syntax.instantiate e2 e1'
                and u2  = Syntax.instantiate_ty e2 u2
                in whnf ctx e1' u2

              (* norm-app-other *)
              | _ ->
                Syntax.mk_app ~loc x u1 u2 e1 e2
        end
      
    | Syntax.Type -> e

    | Syntax.Prod _ -> e

    | Syntax.Eq _ -> e

    | Syntax.Refl _ -> e

and equal_ty ctx t1 t2 = equal ctx t1 t2 Syntax.typ

and equal ctx ((_,loc1) as e1) ((_,loc2) as e2) t =
  Syntax.equal e1 e2 ||
    (* xxx should check equations here *)
    begin (* type-directed phase *)
      let ((t',_) as t) = whnf_ty ctx t in
      match t' with

        | Syntax.Type
        | Syntax.Name _
        | Syntax.App _
        | Syntax.Ascribe _ ->
          equal_whnf ctx e1 e2 t

        | Syntax.Prod (x, t1, t2) ->
          let y, ctx = Context.add_fresh x t1 ctx in
          let y = Syntax.mk_name ~loc:Position.Nowhere y in
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
          let y, ctx = Context.add_fresh x u1 ctx in
          let y' = Syntax.mk_name ~loc:Position.Nowhere y in
          let u2  = Syntax.instantiate_ty y' u2
          and u2' = Syntax.instantiate_ty y' u2'
          and e  = Syntax.instantiate y' e
          and e' = Syntax.instantiate y' e'
          in
            equal_ty ctx u2 u2' &&
            equal ctx e e' u2
        end
       
      | Syntax.App ((x,u1,u2), d1, d2), Syntax.App ((_,u1',u2'), d1', d2') ->
        equal_ty ctx u1 u1'
        &&
        begin
          let y, ctx = Context.add_fresh x u1 ctx in
          let y' = Syntax.mk_name ~loc:Position.Nowhere y in
          let u2  = Syntax.instantiate_ty y' u2
          and u2' = Syntax.instantiate_ty y' u2'
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
        
      | Syntax.Type, Syntax.Type -> true

      | Syntax.Prod (x, u1, u2), Syntax.Prod (_, u1', u2') ->
        equal_ty ctx u1 u1' &&
        begin 
          let y, ctx = Context.add_fresh x u1 ctx in
          let y' = Syntax.mk_name ~loc:Position.Nowhere y in
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

      | (Syntax.Name _ | Syntax.Ascribe _ | Syntax.Lambda _ | Syntax.App _ |
          Syntax.Type | Syntax.Prod _ | Syntax.Eq _ | Syntax.Refl _), _ ->
        false

    end

let as_prod ctx t =
  let (t',_) = whnf_ty ctx t in
    match t' with
      | Syntax.Prod (x, t1, t2) -> (x, t1, t2)
      | _ ->
        Error.typing "product expected but found %t"
          (Print.ty ctx t)
        
                
