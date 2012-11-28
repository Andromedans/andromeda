(* Desugaring of input syntax to syntax with de Bruijn indices. *)

let index ~loc x =
  let rec index k = function
    | [] -> Error.typing "unknown identifier %t" (Print.variable x)
    | y :: ys -> if x = y then k else index (k + 1) ys
  in
    index 0

let desugar xs =
  let rec desugar xs (e, loc) =
    match e with
      | Input.Var x -> Syntax.Var (index ~loc x env)
      | Input.Universe u -> Syntax.Universe u
      | Input.Pi a -> Syntax.Pi (desugar_abstraction env a)
      | Input.Lambda a -> Syntax.Lambda (desugar_abstraction env a)
      | Input.App (e1, e2) -> Syntax.App (desugar e1, desugar e2)
  and desugar_abstraction env (x, t, e) =
    (desugar env t, desugar (x :: env) e)
  in
    desugar []
