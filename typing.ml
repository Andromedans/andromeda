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
      let t = Common.nowhere (fresh_tvar' ()) in
      let x = fresh_evar' ctx t in
        (x, loc), t, cnstr
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
  let cnstr = Unify.add_constraint ~loc:(snd e) ctx cnstr t' t in
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
let toplevel_infer ctx e =
  let e, t, cnstr = infer ctx [] e in
  let sbst = solve cnstr in
    Syntax.subst sbst e,
    Syntax.subst sbst t
