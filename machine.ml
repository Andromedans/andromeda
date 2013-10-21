(** Abstract machine for evaluating computations. *)

open Context
open Value

type handler =
  | BuiltinHandler of (Context.context -> Syntax.operation -> Value.result)

let rec to_term ctx = function
  | Lambda (x, t, v) ->
    let e, s = to_term (add_parameter x t ctx) v in
      Syntax.mk_lambda x (Some t) e, Syntax.mk_pi x t s

let rec to_witness ctx t =
  match fst (Norm.whnf ctx t) with
    | Syntax.Pi (x, t1, t2) ->
      let w = to_witness (add_parameter x t1 ctx) t2 in
        Lambda (x, t1, w)
    | _ ->
      Error.runtime ~loc:(snd t)
        "this expression has type %t but it shoud be a witness or a function" (Print.expr ctx.names t)

let pattern_match (p1, p2, s) (e1, e2, t) =
  Syntax.alpha_equal p1 e1 && Syntax.alpha_equal p2 e2 && Syntax.alpha_equal s t

let rec sequence k = function
  | Value v -> 
    k v
  | Abstraction (x, t, r, k') ->
    let k'' u = sequence k (k' u) in
      Abstraction (x, t, r, k'')
  | Definition (x, t, e, r, k') ->
    let k'' u = sequence k (k' u) in
      Definition (x, t, e, r, k'')
  | Operation (op, k') ->
      let k'' u = sequence k (k' u) in
        Operation (op, k'')

let top_handler ctx (op, loc) =
  match op with
    | Syntax.Inhabit t ->
      ignore (Typing.check_sort ctx t) ;
      Error.runtime ~loc "sorry, this has not been implemented yet" (Print.expr ctx.names t)

let find_handler_case (op, _) lst =
  match op with
    | Syntax.Inhabit _  -> None

let shift_handler = function
  | BuiltinHandler _ as h -> h

let rec eval_handler ctx h op k =
  match h with
    | BuiltinHandler f -> 
      let r = f ctx op in sequence k r

(** [handle ctx h c] handles computation [c] in context [ctx] using handler [h]. *)
and handle ctx h = function
  | Value _ as v -> v
  | Abstraction (x, t, r, k) ->
    ignore (Typing.check_sort ctx t) ;
    let h = shift_handler h in
      (match handle (add_parameter x t ctx) h r with
        | Value v -> k (Lambda (x, t, v))
        | (Operation _ | Abstraction _ | Definition _) as r -> Abstraction (x, t, r, k))
  | Definition (x, t, e, r, k) ->
    (* XXX ignore (Typing.check ctx e t) ; *)
    let h = shift_handler h in
      (match handle (add_definition x t e ctx) h r with
        | Value v -> k (Lambda (x, t, v))
        | (Operation _ | Abstraction _ | Definition _) as r -> Definition (x, t, e, r, k))
  | Operation (op, k) -> eval_handler ctx h op (fun v -> handle ctx h (k v))

and eval ctx (c, loc) =
  match c with
    | Syntax.Return e ->
      let t = Typing.infer ctx e in
        Value (to_witness ctx t)
    | Syntax.Abstraction (x, t, c) ->
      ignore (Typing.check_sort ctx t) ;
      let r = eval (add_parameter x t ctx) c in
        Abstraction (x, t, r, (fun v -> Value v))
    | Syntax.Operation op ->
      Operation (op, (fun v -> Value v))
    | Syntax.Handle (c, h) ->
      failwith "machine.ml, eval, Not implemented"
    | Syntax.Let (x, c1, c2) ->
      let r = eval ctx c1 in
        sequence (fun v ->
          let e, t = to_term ctx v in
          let r = eval (add_definition x t e ctx) c2 in
            Definition (x, t, e, r, (fun v -> Value v)))
          r

let toplevel ctx c =
  let rec run r =
    let r = handle ctx (BuiltinHandler top_handler) r in
    match r with
      | Value v -> v
      | _ -> run r
  in
    run (eval ctx c)

let toplet ctx x c =
  let v = toplevel ctx c in
  let e, t = to_term ctx v in
    add_definition x t e ctx

