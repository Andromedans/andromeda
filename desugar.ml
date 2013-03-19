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
    | Input.Pi (x, t1, t2) -> Syntax.Pi (x, expr xs t1, expr (x :: xs) t2)
    | Input.Lambda (x, None, e) -> Syntax.Lambda (x, None, expr (x :: xs) e)
    | Input.Lambda (x, Some t, e) -> Syntax.Lambda (x, Some (expr xs t), expr (x :: xs) e)
    | Input.App (e1, e2) -> Syntax.App (expr xs e1, expr xs e2)
    | Input.Ascribe (e, t) -> Syntax.Ascribe (expr xs e, expr xs t)
    | Input.EqJdg (e1, e2, t) -> Syntax.EqJdg (expr xs e1, expr xs e2, expr xs t)
    | Input.TyJdg (e, t) -> Syntax.TyJdg (expr xs e, expr xs t)), 
  loc

let sort = expr

let operation xs (op, loc) =
  (match op with
    | Input.Inhabit t -> Syntax.Inhabit (sort xs t)
    | Input.Infer e -> Syntax.Infer (expr xs e)
    | Input.HasType (e, t) -> Syntax.HasType (expr xs e, sort xs t)
    | Input.Equal (e1, e2, t) -> Syntax.Equal (expr xs e1, expr xs e2, sort xs t)),
  loc

let rec computation xs (c, loc) =
  (match c with
    | Input.Abstraction (x, t, c) -> Syntax.Abstraction (x, sort xs t, computation (x :: xs) c)
    | Input.Operation op -> Syntax.Operation (operation xs op)
    | Input.Handle (c, h) -> Syntax.Handle (computation xs c, handler xs h)
  ),
  loc

and handler xs lst = List.map (handler_case xs) lst

and handler_case xs (e1, e2, s, e) =
  (expr xs e1, expr xs e2, sort xs s, expr xs e)
