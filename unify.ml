type solution = (Syntax.meta_variable * Syntax.expr) list

type equation = Common.position * Syntax.context * Syntax.expr * Syntax.expr

type constr = equation list * solution
      
let add_equation ~loc ctx cnstr e1 e2 =
  if e1 = e2 then cnstr else ([(loc, ctx, e1, e2)], []) :: cnstr

exception UnificationFailed

(** An equation is reduced to give a substitution of existential variables
    and further equations that need to be resolved before the substitution
    becomes type-safe. *)
let reduce_equation sbst (loc, ctx, e1, e2) =
  let v1 = Hnf.hnf ctx (Syntax.subst sbst e1) in
  let v2 = Hnf.hnf ctx (Syntax.subst sbst e2) in
    try begin
      match v1, v2 with
        | Hnf.Spine (Hnf.EVar (x1, ctx1, t1), lst1), Hnf.Spine (Hnf.EVar (x2, ctx2, t2), lst2) ->
          (* Both EVar *)
          if List.length lst1 <> List.length lst2 then raise UnificationFailed ;
          (Syntax.extend_evar x1 (Syntax.mk_evar (x2, ctx2, t2)) Syntax.empty_subst),
            


      | Hnf.Spine (Hnf.EVar x1, lst1), (Hnf.Spine (Hnf.Var _, _) | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _)
      | (Hnf.Spine (Hnf.Var _, _) | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _), Hnf.Spine (Hnf.EVar x1, lst1) ->
          (* One EVar, the other not *)
        begin match solve_evar x1 lst1 (Hnf.reify v2) with
          | Some _ -> failwith "now what?"
          | None -> Error.typing ~loc "unable to solve the equation@ %t = %t" (Print.expr e1) (Print.expr e2)
        end
      | Hnf.Spine (Hnf.Var x1, lst1), Hnf.Spine (Hnf.Var x2, lst2) ->
          (* Both Var *)
        if x1 = x2 && List.length lst1 = List.length lst2
        then (sbst, List.map2 (fun e1 e2 -> (loc, ctx, e1, e2)) lst1 lst2)
        else Error.typing ~loc "unable to solve the equation@ %t = %t" (Print.expr e1) (Print.expr e2)
      | Hnf.Universe u1, Hnf.Universe u2 ->
        (match Universe.solve u1 u2 sbst.uvars with
          | None -> Error.typing ~loc "unable to solve the universe level equation@ %t = %t" (Print.universe u1) (Print.universe u2)
          | Some uvars -> { sbst with uvars = uvars }, [])
      | Hnf.Pi (x1, t1, e1), Hnf.Pi (x2, t2, e2) -> failwith "not implemented"
      | Hnf.Lambda (x1, t1, f1), Hnf.Lambda (x2, t2, f2) -> failwith "not implemented"
      | (Hnf.Spine _ | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _), _ ->
        Error.typing ~loc "%t and %t are not equal" (Print.expr e1) (Print.expr e2)
    end
    with UnificationFailed -> Error.typing ~loc "cannot solve %t = %t" (Print.expr e1) (Print.expr e2)
  in
  ()

(** A constraint is a list of equations with a substitution. When the equations
    have been reduced, the substitution becomes type-safe. *)
let reduce_constraint sbst (eqs, sltn) =
  Collection.fold
    (fun (eqs, sltn) eq ->
      let (es, s) = reduce_equation sbst eq
    )
    (Collection.empty, sbst) eqs

(** [reduce sltn cnstr] accepts a partial solution [sltn] of the unification problem [cnstr]
    and returns the updated solution with remaining constraints. *)
let reduce =
  let reduce1 sltn cnstr =
    List.fold_left
      (fun (progress, sltn, remaining) c ->
        match reduce_constraint sltn c with
          | None -> (progress, sltn, remaining)
          | Some (s, r) -> (true, compose_subst sltn s, r @ remaining))
      (false, sltn, [])
      cnstr
  in
  let rec loop sltn cnstr =
    let (progress, sltn, cnstr) = reduce1 question answer in
      if progress
      then loop cnstr sltn
      else (cnstr, sltn)
  in
    loop


let solve cnstr =
  let solve_evar (x, ctx, lst) args e =
    (* Check that [args] are distinct variables, should probably refresh them. *)
    (* Check that [e] is ok in [ctx] extended with [args] (where do types of [args] come from?) *)
    failwith "solve_evar"
  in
  let solve1 (loc, ctx, e1, e2) sbst =
    Print.debug "Solving %t =@ %t" (Print.expr e1) (Print.expr e2) ;
    let v1 = Hnf.hnf ctx (Syntax.subst sbst e1) in
    let v2 = Hnf.hnf ctx (Syntax.subst sbst e2) in
      match v1, v2 with
        | Hnf.Spine (Hnf.EVar x1, lst1), Hnf.Spine (Hnf.EVar x2, lst2) ->
          (* Both EVar *)
          failwith "both evar"
        | Hnf.Spine (Hnf.EVar x1, lst1), (Hnf.Spine (Hnf.Var _, _) | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _)
        | (Hnf.Spine (Hnf.Var _, _) | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _), Hnf.Spine (Hnf.EVar x1, lst1) ->
          (* One EVar, the other not *)
          begin match solve_evar x1 lst1 (Hnf.reify v2) with
            | Some _ -> failwith "now what?"
            | None -> Error.typing ~loc "unable to solve the equation@ %t = %t" (Print.expr e1) (Print.expr e2)
          end
        | Hnf.Spine (Hnf.Var x1, lst1), Hnf.Spine (Hnf.Var x2, lst2) ->
          (* Both Var *)
          if x1 = x2 && List.length lst1 = List.length lst2
          then (sbst, List.map2 (fun e1 e2 -> (loc, ctx, e1, e2)) lst1 lst2)
          else Error.typing ~loc "unable to solve the equation@ %t = %t" (Print.expr e1) (Print.expr e2)
        | Hnf.Universe u1, Hnf.Universe u2 ->
          (match Universe.solve u1 u2 sbst.uvars with
            | None -> Error.typing ~loc "unable to solve the universe level equation@ %t = %t" (Print.universe u1) (Print.universe u2)
            | Some uvars -> { sbst with uvars = uvars }, [])
        | Hnf.Pi (x1, t1, e1), Hnf.Pi (x2, t2, e2) -> failwith "not implemented"
        | Hnf.Lambda (x1, t1, f1), Hnf.Lambda (x2, t2, f2) -> failwith "not implemented"
        | (Hnf.Spine _ | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _), _ ->
          Error.typing ~loc "%t and %t are not equal" (Print.expr e1) (Print.expr e2)
  in
  let rec loop sbst = function
    | [] -> sbst
    | c :: cnstr ->
      let sbst, cnstr' = solve1 c sbst in
        loop sbst (cnstr' @ cnstr)
  in
    loop Syntax.empty_subst cnstr

