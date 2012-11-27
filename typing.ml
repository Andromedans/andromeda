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

exception UnificationFailure of Syntax.substitution

let solve_evar x e sltn =
  compose_subst sltn (extend_evar x e empty_subst)

(** [infer ctx e] infers the type of expression [e] of type [Input.expr] in context [ctx]. 
    It returns the expression converted to type [expr], its type, and a solution for
    the existential variables. *)
let rec infer (ctx : context) sltn (e, loc) : expr * expr * _ =
  match e with
    | Input.Var x ->
      let t =
        try lookup_ty x ctx
        with Not_found -> Error.typing ~loc "unkown identifier %t" (Print.variable x)
      in
        (Var x, loc), t, sltn
    | Input.Underscore ->
      let t = fresh_tvar () in
      let x = fresh_evar ~loc:loc ctx t in
        x, t, sltn
    | Input.Universe u -> 
      let u, sltn = Universe.infer ctx sltn u in
        (Universe u, loc),
        mk_universe (Universe.succ u),
        sltn
    | Input.Pi (x, t1, t2) ->
      let t1, u1, sltn = infer_universe ctx sltn t1 in
      let t2, u2, sltn = infer_universe (extend x t1 ctx) sltn t2 in
        (Pi (x, t1, t2), loc),
        mk_universe (Universe.umax u1 u2),
        sltn
    | Input.Lambda (x, t, e) ->
      let t, u, sltn = infer_universe ctx sltn t in
      let e, te, sltn = infer (extend x t ctx) sltn e in
        (Lambda (x, t, e), loc),
        mk_pi (x, t, te),
        sltn
    | Input.App (e1, e2) ->
      let e1, (x, s, t), sltn = infer_pi ctx sltn e1 in
      let e2, s, sltn = check ctx sltn e2 s in
        (App (e1, e2), loc), 
        subst (extend_var x e2 empty_subst) t,
        sltn
    | Input.Ascribe (e, t) -> 
      let t, _, sltn = infer_universe ctx sltn t in
        check ctx sltn e t

(** [infer_universe ctx t] infers the universe level of type [t] in context [ctx]. *)
and infer_universe ctx sltn t =
  let v = Universe.fresh () in
  let t, _, sltn = check ctx sltn t (mk_universe v) in
    t, v, sltn

(** [infer_pi ctx e] infers the type of [e] in context [ctx], verifies that it is
    of the form [Pi (x, t1, t2)] and returns the triple [(x, t1, t2)]. *)
and infer_pi ctx sltn e =
  let x = Common.refresh (Common.String "x") in
  let t1 = fresh_tvar () in
  let u = mk_universe (Universe.fresh ()) in
  let t2 = fresh_evar ctx (mk_arrow t1 u) in
  let a = (x, t1, mk_app t2 (mk_var x)) in
  let e, _, sltn = check ctx sltn e (mk_pi a) in
    e, a, sltn

(** [check ctx e t] checks that expression [e] of type [Input.expr] has type [t] in
    context [ctx]. It returns the expression converted to [expr] and a list of
    constraints to be solved.
*)
and check ctx sltn ((_, loc) as e) (t : expr) =
  let e, t', sltn = infer ctx sltn e in
    try
      let sltn = solve_expr ctx sltn t' t in
        e, t, sltn
    with UnificationFailure sltn ->
      let e = Syntax.subst sltn e in
      let t = Syntax.subst sltn t in
        Error.typing ~loc "%t should have type %t" (Print.expr e) (Print.expr t)

and solve sltn eqs =
  List.fold_left
    (fun sltn (ctx, e1, e2) -> compose_subst (solve_expr ctx sltn e1 e2) sltn)
    sltn eqs

and solve_expr ctx sltn e1 e2 =
  let e1 = Syntax.subst sltn e1 in
  let e2 = Syntax.subst sltn e2 in
  Print.debug "Now solving expressions %t = %t." (Print.expr e1) (Print.expr e2) ;
    match Hnf.hnf ctx e1, Hnf.hnf ctx e2 with
      | Hnf.EVar ((m, ctx', t), xs), e | e, Hnf.EVar ((m, ctx', t), xs) ->
        let  f =
          List.fold_left
            (fun e x ->
              let t = try lookup_ty x ctx with Not_found -> assert false in
                mk_lambda (x, t, e))
            (Hnf.reify e) xs
        in
          Print.debug "SOLVED FOR %d <--- %t" m (Print.expr f) ;
          solve_evar m f sltn

      | Hnf.Var x, Hnf.Var y ->
        if x = y then sltn else raise (UnificationFailure sltn)

      | Hnf.App (v1, e1), Hnf.App (v2, e2) ->
        let sltn = solve_expr ctx sltn (Hnf.reify v1) (Hnf.reify v2) in
          solve_expr ctx sltn e1 e2

      | Hnf.Universe u1, Hnf.Universe u2 ->
        (match Universe.solve u1 u2 sltn.uvars with
          | None -> raise (UnificationFailure sltn)
          | Some uvars -> { sltn with uvars = uvars })

      | Hnf.Pi (x1, t1, e1), Hnf.Pi (x2, t2, e2) ->
        let sltn = solve_expr ctx sltn t1 t2 in
        let y = Common.refresh x1 in
          solve_expr (extend y t1 ctx) sltn (rename_var x1 y e1) (rename_var x2 y e2)

      | Hnf.Lambda (x1, t1, f1), Hnf.Lambda (x2, t2, f2) ->
        let sltn = solve_expr ctx sltn t1 t2 in
        let y = Common.refresh x1 in
        let var_y = mk_var y in
          solve_expr (extend y t1 ctx) sltn (Hnf.reify (f1 var_y)) (Hnf.reify (f2 var_y))

      | (Hnf.Var _ | Hnf.App _ | Hnf.Universe _ | Hnf.Pi _ | Hnf.Lambda _), _ ->
        raise (UnificationFailure sltn)

let toplevel_infer ctx e =
  let e, t, sltn = infer ctx empty_subst e in
    Syntax.subst sltn e,
    Syntax.subst sltn t

let toplevel_infer_universe ctx e =
  let e, u, sltn = infer_universe ctx empty_subst e in
    Syntax.subst sltn e,
    Syntax.subst sltn (mk_universe u)
