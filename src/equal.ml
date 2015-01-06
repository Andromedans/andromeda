(** The whnf of a type [t] in context [ctx]. *)
let rec whnf_ty ctx (Value.Ty t) =
  let t = whnf ctx t
  in Value.ty t

(** The whnf of term [e] in context [ctx]. *)
and whnf ctx ((e',loc) as e) =
  match e' with

    | Value.Spine (e, ([], _)) -> whnf ctx e
    | Value.Lambda ([], (e, _)) -> whnf ctx e
    | Value.Prod ([], Value.Ty e) -> whnf ctx e

    | Value.Spine (e, ((_ :: _) as xets, t)) -> whnf_spine ~loc ctx e xets t

    | Value.Lambda (_ :: _, _)
    | Value.Prod (_ :: _, _)
    | Value.Name _
    | Value.Type
    | Value.Eq _
    | Value.Refl _ -> e

    | Value.Bound _ ->
       Error.impossible ~loc "de Bruijn encountered in whnf"

(** The whnf of a spine [Spine (e, (xets, t))] in context [ctx]. *)
and whnf_spine ~loc ctx e xets t =
  let (e',eloc) as e = whnf ctx e in
  match e' with

  | Value.Lambda (xus, (e, u)) ->
    begin
      match beta ~loc:eloc ctx xus e u xets t with
      | None -> Value.mk_spine ~loc e xets t
      | Some e -> whnf ctx e
    end

  | Value.Spine _
  | Value.Name _
  | Value.Type
  | Value.Prod _
  | Value.Eq _
  | Value.Refl _ ->
    Value.mk_spine ~loc e xets t

  | Value.Bound _ ->
    Error.impossible ~loc "de Bruijn encountered in whnf"

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
      if equal_abstracted_ty ctx xuvs u' t'
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

(** Let [xuus] be the list [(x1,u1,u1'); ...; (xn,un,un')] where
    [ui]  is well-formed in the context [x1:u1 , ..., x{i-1}:u{i-1} ] and
    [ui'] is well-formed in the context [x1:u1', ..., x{i-1}:u{i-1}'] and
    [v]  is well-formed in the context [x1:u1, ..., xn:un] and
    [v'] is well-formed in the context [x1:u1',..., xn:un'].
    We verify that the [ui] are equal to [ui'] and that [v] is equal to [v]. *)
and equal_abstracted_ty ctx xuus v v' =
  (* As we descend into the contexts we carry around a list of variables
     [ys] with which we unabstract the bound variables. *)
  let rec eq ys ctx =
    function
     | [] -> 
        let v = Value.unabstract_ty ys 0 v
        and v' = Value.unabstract_ty ys 0 v'
        in equal_ty ctx v v'
     | (x,u,u')::xuus ->
        let u  = Value.unabstract_ty ys 0 u
        and u' = Value.unabstract_ty ys 0 u'
        in
          equal_ty ctx u u'
          &&
          (let y, ctx = Context.add_fresh x u ctx in
             eq (ys @ [y]) ctx xuus) (* XXX optimize list append *)
   in
     eq [] ctx xuus
 
(** Compare two types *)
and equal_ty ctx (Value.Ty t1) (Value.Ty t2) = equal ctx t1 t2 Value.typ

and equal ctx ((_,loc1) as e1) ((_,loc2) as e2) t =
  Value.equal e1 e2 ||
    (* xxx should check equations here *)
    begin (* type-directed phase *)
      let Value.Ty ((t',_) as t) = whnf_ty ctx t in
      match t' with

        | Value.Type
        | Value.Name _
        | Value.Spine _ ->
          equal_whnf ctx e1 e2 t

        | Value.Prod (xus, u) ->
            let rec fold ctx ys xyus =
              begin function
              | (x, (Value.Ty (_, loc) as u)) :: xus ->
                  let v = Value.unabstract_ty ys 0 u in
                  let y, ctx = Context.add_fresh x v ctx in
                  fold ctx (ys @ [y]) (xyus @ [(x, (Value.mk_name ~loc y, u))]) xus
              | [] ->
                  let v = Value.unabstract_ty ys 0 u
                  and e1 = Value.mk_spine ~loc:loc1 e1 xyus u
                  and e2 = Value.mk_spine ~loc:loc2 e2 xyus u
                  in equal ctx e1 e2 v
              end
            in fold ctx [] [] xus

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

      | Value.Lambda (xus, (e1, t1)), Value.Lambda (xvs, (e2, t2)) ->
          let rec zip ys ctx = function
          | (x, u) :: xus, (_, u') :: xvs ->
              let u  = Value.unabstract_ty ys 0 u
              and u' = Value.unabstract_ty ys 0 u'
              in
              equal_ty ctx u u' &&
              let y, ctx = Context.add_fresh x u ctx in
              zip (ys @ [y]) ctx (xus, xvs) (* XXX optimize list append *)
          | ([] as xus), xvs | xus, ([] as xvs) ->
              let t1' = Value.mk_prod_ty ~loc:Position.nowhere xus t1
              and t2' = Value.mk_prod_ty ~loc:Position.nowhere xvs t2 in
              let t1' = Value.unabstract_ty ys 0 t1'
              and t2' = Value.unabstract_ty ys 0 t2'
              in
              equal_ty ctx t1' t2' &&
              let e1 = Value.mk_lambda ~loc:(snd e1) xus e1 t1
              and e2 = Value.mk_lambda ~loc:(snd e2) xvs e2 t2
              in
              let e1 = Value.unabstract ys 0 e1
              and e2 = Value.unabstract ys 0 e2
              in
              equal ctx e1 e2 t1'
          in
          zip [] ctx (xus, xvs)

      | Value.Spine (e1, (xets1, t1)), Value.Spine (e2, (xets2, t2)) ->
          equal_spine ~loc:loc1 ctx e1 xets1 t1 e2 xets2 t2

      | Value.Type, Value.Type -> true

      | Value.Prod (xus, t1), Value.Prod (xvs, t2) ->
          let rec zip xuvs = function
          | (x, u) :: xus, (_, v) :: xvs ->
            zip ((x, u, v) :: xuvs) (xus, xvs)
          | ([] as xus), xvs | xus, ([] as xvs) ->
              let xuvs = List.rev xuvs in
              let t1 = Value.mk_prod_ty ~loc:loc1 xus t1
              and t2 = Value.mk_prod_ty ~loc:loc2 xvs t2 in
              equal_abstracted_ty ctx xuvs t1 t2
          in
          zip [] (xus, xvs)

      | Value.Eq (u, d1, d2), Value.Eq (u', d1', d2') ->
        equal_ty ctx u u' &&
        equal ctx d1 d1' u &&
        equal ctx d2 d2' u

      | Value.Refl (u, d), Value.Refl (u', d') ->
        equal_ty ctx u u' &&
        equal ctx d d' u

      | (Value.Name _ | Value.Lambda _ | Value.Spine _ |
          Value.Type | Value.Prod _ | Value.Eq _ | Value.Refl _), _ ->
        false

    end

and equal_spine ~loc ctx e1 xets1 t1 e2 xets2 t2 =
  List.length xets1 = List.length xets2 &&
  begin
    let rec zip es1 es2 = function
    | (x, (e1, t1)) :: xets1, (_, (e2, t2)) :: xets2 ->
        let t1 = Value.instantiate_ty es1 0 t1
        and t2 = Value.instantiate_ty es2 0 t2 in
        equal_ty ctx t1 t2 &&
        equal ctx e1 e2 t1 &&
        zip es1 es2 (xets1, xets2) 
    | [], [] ->
        let t1 = Value.instantiate_ty es1 0 t1
        and t2 = Value.instantiate_ty es2 0 t2 in
        equal_ty ctx t1 t2 &&
        equal ctx e1 e2 t1
    | _ :: _, [] | [], _ :: _ -> Error.impossible ~loc "you will not get a beer if you do not report this error";
    in
    zip [] [] (xets1, xets2)
  end
