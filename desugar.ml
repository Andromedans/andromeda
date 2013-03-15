(** Desugaring of input syntax to internal syntax. *)

(** [index ~loc x xs] finds the location of [x] in the list [xs]. *)
let index ~loc x =
  let rec index k = function
    | [] -> Error.typing ~loc "unknown identifier %s" x
    | y :: ys -> if x = y then k else index (k + 1) ys
  in
    index 0

(** [expr xs e] converts an expression of type [Input.expr] to type [Syntax.expr] by
    replacing names in [e] with de Bruijn indices. Here [xs] is the list of names
    currently in scope (i.e., Context.names) *)
let rec expr xs (e, loc) =
  (match e with
    | Input.Var x -> Syntax.Var (index ~loc x xs)
    | Input.Type -> Syntax.Type
    | Input.Eq (t, e1, e2) -> Syntax.Eq (expr xs t, expr xs e1, expr xs e2)
    | Input.Pi (x, t1, t2) -> Syntax.Pi (x, expr xs t1, expr (x :: xs) t2)
    | Input.Lambda (x, None, e) -> Syntax.Lambda (x, None, expr (x :: xs) e)
    | Input.Lambda (x, Some t, e) -> Syntax.Lambda (x, Some (expr xs t), expr (x :: xs) e)
    | Input.App (e1, e2) -> Syntax.App (expr xs e1, expr xs e2)
    | Input.Ascribe (e, t) -> Syntax.Ascribe (expr xs e, expr xs t)),
  loc

(** [computation xs c] converts a computation of type [Input.computation]
    to type [Syntax.computation]. *)
let rec computation xs (c, loc) =
  (match c with
    | Input.Infer e -> Syntax.Infer (expr xs e)
    | Input.Check (e1, e2) -> Syntax.Check (expr xs e1, expr xs e2)),
  loc
