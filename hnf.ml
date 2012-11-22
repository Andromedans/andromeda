(** Weak head-normal forms. *)

type variable = Syntax.variable

type meta_variable = Syntax.meta_variable

type expr = Syntax.expr

type universe = Universe.universe

(** The type of head normal forms. *)
type hnf =
  | Spine of head * expr list (* the arguments are in reverse order *)
  | Universe of universe
  | Pi of Syntax.abstraction
  | Lambda of abstraction

and abstraction = variable * expr * (expr -> hnf)

and head =
  | Var of variable
  | EVar of meta_variable

let hnf ctx =
  let rec hnf (env : (Syntax.variable * expr) list) (e, loc) =
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
                | None -> Spine (Var x, [])
                | Some e -> hnf env e
            end
        end
      | Syntax.EVar (x, ctx, t) -> Spine (EVar (x, ctx, t), [])
      | Syntax.Universe k -> Universe k
      | Syntax.Pi a -> Pi a
      | Syntax.Lambda (x, t, e) -> Lambda (x, t, fun e' -> hnf ((x, e') :: env) e)
      | Syntax.Spine (e1, e2) ->
        (match hnf env e1 with
          | Lambda (x, _, f) -> f e2
          | Spine (h, lst) -> Spine (h, e2 :: lst)
          | Universe _ | Pi _ -> Error.runtime ~loc:(snd e2) "Function expected")
      | Syntax.Ascribe (e, _) -> hnf env e
  in
    hnf []

let rec reify = function
  | Spine (h, lst) ->
    List.fold_right (fun e h -> Syntax.mk_app h e) lst (reify_head h)
  | Universe u -> Syntax.mk_universe u
  | Pi a -> Syntax.mk_pi a
  | Lambda (x, t, f) -> 
    let x = Common.refresh x in
      Syntax.mk_lambda (x, t, reify (f (Syntax.mk_var x)))

and reify_head = function
  | Var x -> Syntax.mk_var x
  | EVar (x, ctx, t) -> Syntax.mk_evar (x, ctx, t)
