open Syntax

let disable_typing = ref false

let lookup_var x ctx =
  match Common.lookup x ctx with
    | Some y -> y
    | None -> Error.typing "unkown identifier %t" (Print.variable x)

let rec infer_type ctx = function
  | Var x -> lookup_var x ctx
  | Universe u -> Universe (u + 1)
  | Pi (x, t1, t2) ->
    let u1 = infer_universe ctx t1 in
    let u2 = infer_universe (Common.extend x t1 ctx) t2 in
      Universe (max u1 u2)
  | Lambda (x, t, e) ->
    check_type ctx t ;
    let s = infer_type (Common.extend x t ctx) e in
      Pi (x, t, s)
  | App (e1, e2) ->
    let (t, f) = infer_pi ctx e1 in
    let r = infer_type ctx e2 in
      check_equal t r ;
      f e2

and infer_universe ctx t =
  let u = infer_type ctx t in
    match Value.eval [] u with
      | Value.Universe u -> u
      | Value.Neutral _ | Value.Pi _ | Value.Lambda _ -> Error.typing "type expected"

and check_type ctx t = ignore (infer_universe ctx t)

and infer_pi ctx e =
  let t = infer_type ctx e in
    match Value.eval [] t with
      | Value.Pi (t, _, f) -> (Value.uneval t, fun e -> Value.uneval (f (Value.eval [] e)))
      | Value.Universe _ | Value.Neutral _ | Value.Lambda _ -> Error.typing "function expected"

and check_equal t1 t2 =
  if not (Value.equal_value (Value.eval [] t1) (Value.eval [] t2))
  then Error.typing "type mismatch"
