(** Let [xuus] be the list [(x1,u1,u1'); ...; (xn,un,un')] where
    [ui]  is well-formed in the context [x1:u1 , ..., x{i-1}:u{i-1} ] and
    [ui'] is well-formed in the context [x1:u1', ..., x{i-1}:u{i-1}'] and
    [v]  is well-formed in the context [x1:u1, ..., xn:un] and
    [v'] is well-formed in the context [x1:u1',..., xn:un'].
    We verify that the [ui] are equal to [ui'] and that [v] is equal to [v]
    where we use [equal_u] to compare [ui] and [ui'] and
    [equal_v] to compare [v] and [v']. *)
let equal_abstraction equal_u equal_v ctx xuus v v' =
  (* As we descend into the contexts we carry around a list of variables
     [ys] with which we unabstract the bound variables. *)
  let rec eq ys ctx =
    function
     | [] -> 
        let v = Value.unabstract_ty ys 0 v
        and v' = Value.unabstract_ty ys 0 v'
        in equal_v ctx v v'
     | (x,u,u')::us ->
        let u  = Value.unabstract_ty ys 0 u
        and u' = Value.unabstract_ty ys 0 u'
        in
          equal_u ctx u u'
          &&
          (let y, ctx = Context.add_fresh x u ctx in
             eq (ys @ [y]) ctx us) (* XXX optimize list append *)
   in
     eq [] ctx xuus

(** The whnf of a type [t] in context [ctx]. *)
let rec whnf_ty ctx (Value.Ty t) =
  let t = whnf ctx t
  in Value.ty t

(** The whnf of term [e] in context [ctx]. *)
and whnf ctx ((e',loc) as e) =
  match e' with

    | Value.Spine (e, (xets, t)) ->
      whnf_spine ~loc ctx e xets t

    | Value.Lambda ([], (e, _)) ->
      whnf ctx e

    | Value.Lambda (_::_, _)
    | Value.Name _
    | Value.Type
    | Value.Prod _
    | Value.Eq _
    | Value.Refl _ -> e

    | Value.Bound _ ->
       Error.impossible ~loc "de Bruijn encountered in whnf"


(** The whnf of a spine [Spine (e, (xets, t))] in context [ctx]. *)
and whnf_spine ~loc ctx e xets t =
  let (e',eloc) as e = whnf ctx e
  in
    match xets with

    | [] -> e

    | _::_ ->
      begin
        match e' with

        | Value.Lambda (xus, (e, u)) ->
          begin
            match beta ~loc:eloc ctx xus e u xets t with
            | None -> Value.mk_spine ~loc e xets t
            | Some e -> whnf ctx e
          end

        | Value.Spine (e', (xets', t')) ->
          failwith "flattening of spines not implemented"

        | Value.Name _
        | Value.Type
        | Value.Prod _
        | Value.Eq _
        | Value.Refl _ ->
          Value.mk_spine ~loc e xets t

        | Value.Bound _ ->
          Error.impossible ~loc "de Bruijn encountered in whnf"

      end
    
(** Beta reduction of [Lambda (xus, (e, u))] applies to arguments [yevs] at type [t].
    Returns ??? and the unused arguments. *)
and beta ~loc ctx xus e u yevs t =
  let rec split xuvs es xus yevs =
    match xus, yevs with
    | [], _ | _, [] -> List.rev xuvs, List.rev es, xus, yevs
    | (x,u)::xus, (_,(e,v))::yevs -> split ((x,u,v)::xuvs) (e::es) xus yevs
  in
  let xuvs, es, xus, yevs = split [] [] xus yevs
  in
    (* [xuvs] is a list of triples [(x,u,v)] ready to be plugged into [equal_abstraction] *)
    (* [es] is the list of arguments that we are plugging in *)
    (* [xus] is the list of leftover abstraction arguments *)
    (* [yevs] is the list of leftover arguments *)
    (* XXX: optimization -- use the fact that one or both of [xus] and [yevs] are empty. *)
    let yvs = List.map (fun (y, (_, v)) -> (y,v)) yevs in
    let u' = Value.mk_prod_ty ~loc xus u
    and t' = Value.mk_prod_ty ~loc yvs t
    in
      if equal_abstraction
           equal_ty equal_ty ctx
           xuvs
           u' t'
      then
        (* Types match -- we can reduce *)
        let xus, (e, u) =
          Value.instantiate_abstraction
            Value.instantiate_ty Value.instantiate_term_ty
            es 0 (xus, (e, u))
        and yevs, t =
          Value.instantiate_abstraction 
            Value.instantiate_term_ty Value.instantiate_ty
            es 0 (yevs, t)
        in
        let e = Value.mk_lambda ~loc xus e u in
        let e = Value.mk_spine ~loc e yevs t in
          Some e
      else
        (* The types did not match. *)
        None
    

(*
and whnf_spine ~loc ctx ((t',loc) as t) e1 e2 es =
  let rec spine_cod ((t',loc) as t) es =
    begin match t', es with
      | _, [] -> t
      | Value.Prod (_, t1, t2), e::es ->
        let t = Value.instantiate_ty e t2 in
          spine_cod t es
      | _, _ -> Error.impossible ~loc "malformed spine type in whnf_spine, spine_cod"
    end
  in
  match t' with
    | Value.Prod (x,t1,t2) ->
      let (e1',_) as e1 = whnf ctx e1 in
        begin match e1' with
            
          | Value.Spine (t', e', es') when
              (let u = spine_cod t' es in equal_ty ctx u t) ->
            begin match es' @ (e2 :: es) with
              | e2 :: es -> whnf_spine ~loc ctx t' e' e2 es
              | [] -> assert false
            end
              
          | Value.Lambda (_, u1, u2, e') when equal_as_prod ctx x t1 t2 u1 u2 ->
            let e1 = Value.instantiate e2 e'
            and t = Value.instantiate_ty e2 t2
            in begin match es with
              | [] -> whnf ctx e1
              | e2::es -> whnf_spine ~loc ctx t e1 e2 es
            end
              
          | (Value.Name _ | Value.Bound _ | Value.Ascribe _ | Value.Type |
              Value.Prod _ | Value.Eq _ | Value.Refl _ | Value.Spine _ | Value.Lambda _ ) ->
            Value.mk_spine ~loc t e1 (e2::es)

        end

    | _ -> Error.impossible ~loc "malformed spine type in whnf_spine"
 *)

(** Compare two types *)
and equal_ty ctx (Value.Ty t1) (Value.Ty t2) = equal ctx t1 t2 Value.typ

and equal ctx ((_,loc1) as e1) ((_,loc2) as e2) t =
  Value.equal e1 e2 ||
    (* xxx should check equations here *)
    begin (* type-directed phase *)
      let ((t',_) as t) = whnf_ty ctx t in
      match t' with

        | Value.Type
        | Value.Name _
        | Value.Spine _
        | Value.Ascribe _ ->
          equal_whnf ctx e1 e2 t

        | Value.Prod (x, t1, t2) ->
          let y, ctx = Context.add_free x t1 ctx in
          let y = Value.mk_name ~loc:Position.nowhere y in
          let t2 = Value.instantiate_ty y t2
          and e1' = Value.mk_app ~loc:loc1 x t1 t2 e1 y
          and e2' = Value.mk_app ~loc:loc2 x t1 t2 e2 y
          in equal ctx e1' e2' t2

        | Value.Eq _ -> true (** Strict equality *)

        | Value.Bound _ -> Error.impossible ~loc:loc1 "deBruijn encountered in equal"

        | Value.Lambda _ -> Error.impossible ~loc:loc1 "fun is not a type"

        | Value.Refl _ -> Error.impossible ~loc:loc1 "refl is not a type"
    end
    
and equal_whnf ctx e1 e2 t =
  let (e1',loc1) as e1 = whnf ctx e1
  and (e2',loc2) as e2 = whnf ctx e2
  in
    Value.equal e1 e2 ||
    begin match e1', e2' with

      | Value.Name x, Value.Name y -> Common.eqname x y

      | Value.Bound _, _ | _, Value.Bound _ ->
        Error.impossible ~loc:loc1 "deBruijn encountered in equal_whnf"

      | Value.Lambda (x, u1, u2, e), Value.Lambda (_, u1', u2', e') ->
        equal_ty ctx u1 u1'
        &&
        begin
          let y, ctx = Context.add_free x u1 ctx in
          let y' = Value.mk_name ~loc:Position.nowhere y in
          let u2  = Value.instantiate_ty y' u2
          and u2' = Value.instantiate_ty y' u2'
          and e  = Value.instantiate y' e
          and e' = Value.instantiate y' e'
          in
            equal_ty ctx u2 u2' &&
            equal ctx e e' u2
        end
       
      | Value.Spine (t, e, es), Value.Spine (t', e', es') ->
          List.length es = List.length es'
          &&
          equal_ty ctx t t'
          &&
          equal ctx e e' t
          &&
          equal_args ctx t es es'

      | Value.Type, Value.Type -> true

      | Value.Prod (x, u1, u2), Value.Prod (_, u1', u2') ->
        equal_ty ctx u1 u1' &&
        begin 
          let y, ctx = Context.add_free x u1 ctx in
          let y' = Value.mk_name ~loc:Position.nowhere y in
          let u2  = Value.instantiate_ty y' u2
          and u2' = Value.instantiate_ty y' u2'
          in
            equal_ty ctx u2 u2'
        end

      | Value.Eq (u, d1, d2), Value.Eq (u', d1', d2') ->
        equal_ty ctx u u' &&
        equal ctx d1 d1' u &&
        equal ctx d2 d2' u

      | Value.Refl (u, d), Value.Refl (u', d') ->
        equal_ty ctx u u' &&
        equal ctx d d' u

      | (Value.Name _ | Value.Ascribe _ | Value.Lambda _ | Value.Spine _ |
          Value.Type | Value.Prod _ | Value.Eq _ | Value.Refl _), _ ->
        false

    end

and equal_args ctx (t',loc) es es' =
  begin match es, es' with
    | [], [] -> Error.impossible ~loc "comparing empty lists of argumanets in equal_args"
    | [e], [e'] -> 
      begin match t' with
        | Value.Prod (_,t1,t2) -> equal ctx e e' t1
        | _ -> Error.impossible ~loc "malformed spine type in equal_args (1)"
      end
    | e::es, e'::es' ->
      begin match t' with
          (* we do not have to call as_prod here as a spine type must be a [Prod] *)
        | Value.Prod (_,t1,t2) ->
          equal ctx e e' t1 &&
            begin
              let t = Value.instantiate_ty e t2
              in equal_args ctx t es es'
            end
        | _ -> Error.impossible ~loc "malformed spine type in equal_args (2)"
      end
    | [],_::_ | _::_,[] -> false
  end

and as_prod ctx t =
  let (t',_) = whnf_ty ctx t in
    match t' with
      | Value.Prod (x, t1, t2) -> (x, t1, t2)
      | _ ->
        Error.typing "product expected but found %t"
          (Print.ty ctx t)
