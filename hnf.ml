(** Weak head-normal forms. *)

type variable = Syntax.variable

type meta_variable = Syntax.meta_variable

type expr = Syntax.expr

type universe = Universe.universe

(** The type of head normal forms. *)
type hnf =
  | EVar of meta_variable * variable list (* applied in reversed order *)
  | Var of variable
  | App of hnf * expr
  | Universe of universe
  | Pi of Syntax.abstraction
  | Lambda of abstraction

and abstraction = variable * expr * (expr -> hnf)

let hnf ctx =
  let rec hnf env (e, loc) =
    match e with
      | Syntax.Var x ->
        begin
          try hnf env (List.assoc x env)
          with Not_found ->
            begin
              match
                (try Syntax.lookup_value x ctx
                 with Not_found -> Error.runtime ~loc "unkown identifier %t" (Print.variable x))
              with
                | None -> Var x
                | Some e -> hnf env e
            end
        end
      | Syntax.EVar (m, ctx, t) -> EVar ((m, ctx, t), [])
      | Syntax.Universe k -> Universe k
      | Syntax.Pi a -> Pi a
      | Syntax.Lambda (x, t, e) -> Lambda (x, t, fun e' -> hnf ((x, e') :: env) e)
      | Syntax.App (e1, e2) ->
        (match hnf env e1 with
          | Lambda (x, _, f) -> f e2
          | Var _ as e1 -> App (e1, e2)
          | EVar (m, xs) as e1 ->
            (match hnf env e2 with
              | Var y when not (List.mem y xs) -> EVar (m, y :: xs)
              | Var _ | EVar _ | Universe _ | Pi _ | Lambda _ | App _ -> App (e1, e2))
          | App _ | Universe _ | Pi _ -> Error.runtime ~loc:(snd e2) "Function expected")
      | Syntax.Ascribe (e, _) -> hnf env e
  in
    hnf []

let rec reify = function
  | Var x -> Syntax.mk_var x
  | EVar (m, xs) -> List.fold_right (fun x e1 -> Syntax.mk_app e1 (Syntax.mk_var x)) xs (Syntax.mk_evar m)
  | App (e1, e2) -> Syntax.mk_app (reify e1) e2
  | Universe u -> Syntax.mk_universe u
  | Pi a -> Syntax.mk_pi a
  | Lambda (x, t, f) -> 
    let x = Common.refresh x in
      Syntax.mk_lambda (x, t, reify (f (Syntax.mk_var x)))
