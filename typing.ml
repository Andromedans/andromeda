(** Type checking and inference. *)

open Syntax
open Ctx

(** [normalize ctx e] normalizes the given expression [e] in context [ctx]. It removes
    all redexes and it unfolds all definitions. It performs normalization under binders.
    We use the "normalization by evaluation" technique, in which the expression is
    evaluated to an Ocaml value, which is then reified back to an expression. The effect
    of this is that two equal expressions get evaluated to (observationally) equivalent
    values, and hence their reification are syntactically equal (up to renaming of bound
    variables.) *)
let normalize ctx e = Value.reify (Value.eval ctx e)

let normalize' ctx e = Value.reify' (Value.eval' ctx e)

(** [equal ctx e1 e2] compares expressions [e1] and [e2] for equality. *)
let equal ctx e1 e2 = Value.equal (Value.eval' ctx e1) (Value.eval' ctx e2)

(** [infer ctx e] infers the type of expression [e] of type [Input.expr] in context [ctx]. 
    It returns the expression converted to type [expr], its type, and a list
    of constraints. *)
let rec infer (ctx : context) cnstr (e, loc) : expr * expr * _ =
  match e with
    | Input.Var x ->
      let t =
        try lookup_ty x ctx
        with Not_found -> Error.typing ~loc "unkown identifier %t" (Print.variable x)
      in
        (Var x, loc), Common.nowhere t, cnstr
    | Input.Underscore ->
      let t = fresh_tvar' () in
      let x = fresh_evar' ctx (t, loc) in
        (x, loc), Common.nowhere t, cnstr
    | Input.Universe u -> 
      let u, cnstr = Universe.infer ctx cnstr u in
        (Universe u, loc),
        mk_universe (Universe.succ u),
        cnstr
    | Input.Pi (x, t1, t2) ->
      let t1, u1, cnstr = infer_universe ctx cnstr t1 in
      let t2, u2, cnstr = infer_universe (extend x (fst t1) ctx) cnstr t2 in
        (Pi (x, t1, t2), loc),
        mk_universe (Universe.umax u1 u2),
        cnstr
    | Input.Lambda (x, t, e) ->
      let t, u, cnstr = infer_universe ctx cnstr t in
      let e, te, cnstr = infer (extend x (fst t) ctx) cnstr e in
        (Lambda (x, t, e), loc),
        mk_pi (x, t, te),
        cnstr
    | Input.App (e1, e2) ->
      let e1, (x, s, t), cnstr = infer_pi ctx cnstr e1 in
      let e2, s, cnstr = check ctx cnstr e2 s in
        (App (e1, e2), loc), 
        subst (extend_var x (fst e2) empty_subst) t,
        cnstr
    | Input.Ascribe (e, t) -> 
      let t, _, cnstr = infer_universe ctx cnstr t in
        check ctx cnstr e t

(** [check ctx e t] checks that expression [e] of type [Input.expr] has type [t] in
    context [ctx]. It returns the expression converted to [expr] and a list of
    constraints to be solved.

    NB: [check] does *not* check that [t] is a type.
*)
and check ctx cnstr e (t : expr) =
  let e, t', cnstr = infer ctx cnstr e in
  let cnstr = add_constraint ~loc:(snd e) ctx cnstr t' t in
    e, t, cnstr

(** [infer_universe ctx t] infers the universe level of type [t] in context [ctx]. *)
and infer_universe ctx cnstr t =
  let v = Universe.fresh () in
  let t, _, cnstr = check ctx cnstr t (mk_universe v) in
    t, v, cnstr

(** [infer_pi ctx e] infers the type of [e] in context [ctx], verifies that it is
    of the form [Pi (x, t1, t2)] and returns the triple [(x, t1, t2)]. *)
and infer_pi ctx cnstr e =
  let x = Common.refresh (Common.String "x") in
  let t1' = fresh_tvar' () in
  let t1 = Common.nowhere t1' in
  let u = mk_universe (Universe.fresh ()) in
  let t2 = fresh_evar (extend x t1' ctx) (mk_arrow t1 u) in
  let e, _, cnstr = check ctx cnstr e (mk_pi (x, t1, t2)) in
    e, (x, t1, t2), cnstr
      
and add_constraint ~loc ctx cnstr e1 e2 =
  if e1 = e2 then cnstr else (loc, ctx, e1, e2) :: cnstr

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
        | Hnf.App (Hnf.EVar x1, lst1), Hnf.App (Hnf.EVar x2, lst2) ->
          (* Both EVar *)
          failwith "both evar"
        | Hnf.App (Hnf.EVar x1, lst1), (Hnf.App (Hnf.Var _, _) | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _)
        | (Hnf.App (Hnf.Var _, _) | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _), Hnf.App (Hnf.EVar x1, lst1) ->
          (* One EVar, the other not *)
          begin match solve_evar x1 lst1 (Hnf.reify v2) with
            | Some _ -> failwith "now what?"
            | None -> Error.typing ~loc "unable to solve the equation@ %t = %t" (Print.expr e1) (Print.expr e2)
          end
        | Hnf.App (Hnf.Var x1, lst1), Hnf.App (Hnf.Var x2, lst2) ->
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
        | (Hnf.App _ | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _), _ ->
          Error.typing ~loc "%t and %t are not equal" (Print.expr e1) (Print.expr e2)
  in
  let rec loop sbst = function
    | [] -> sbst
    | c :: cnstr ->
      let sbst, cnstr' = solve1 c sbst in
        loop sbst (cnstr' @ cnstr)
  in
    loop Syntax.empty_subst cnstr

let toplevel_infer ctx e =
  let e, t, cnstr = infer ctx [] e in
  let sbst = solve cnstr in
    Syntax.subst sbst e,
    Syntax.subst sbst t
