(** Abstract machine for evaluating computations. *)

open Context
open Value

type handler =
  | EqualityHandler of (Syntax.term * Syntax.term * Syntax.sort * Syntax.term) list
  | BuiltinHandler of (Context.context -> Syntax.operation -> Value.closure -> Value.result)

let pattern_match (p1, p2, s) (e1, e2, t) =
  Syntax.alpha_equal p1 e1 && Syntax.alpha_equal p2 e2 && Syntax.alpha_equal s t

let rec sequence k = function
  | Value v -> k v
  | Abstraction (x, t, r, k') ->
    let k'' u = sequence k (k' u) in
      Abstraction (x, t, r, k'')
  | Operation (op, k') ->
      let k'' u = sequence k (k' u) in
        Operation (op, k'')

let top_handler ctx (op, loc) k =
  match op with
    | Syntax.Inhabit t ->
      ignore (Typing.check_sort ctx t) ;
      Error.runtime ~loc "sorry, this has not been implemented yet" (Print.expr ctx.names t)
    | Syntax.Infer e ->
      let t = Typing.infer ctx e in
        Value.Value (Value.TyWtn (e, t))
    | Syntax.HasType (e, t) ->
      Typing.check ctx e t ;
      Value.Value (Value.TyWtn (e, t))
    | Syntax.Equal (e1, e2, t) ->
      ignore (Typing.check_sort ctx t) ;
      if Typing.equal_at ctx e1 e2 t
      then Value.Value (Value.EqWtn (e1, e2, t))
      else Error.runtime ~loc "do not know how to derive %t" (Print.expr ctx.names (Syntax.mk_eqjdg e1 e2 t))

let find_handler_case (op, _) lst =
  match op with
    | Syntax.Inhabit _ | Syntax.HasType _ | Syntax.Infer _ -> None
    | Syntax.Equal (e1, e2, t) ->
      let rec find = function
        | [] -> None
        | (p1, p2, s, e) :: lst ->
          if pattern_match (p1, p2, s) (e1, e2, t)
          then
            let op = Common.nowhere (Syntax.HasType (e, (Syntax.mk_eqjdg e1 e2 t))) in
              Some (fun k -> Operation (op, k))
          else find lst
      in
        find lst

let shift_handler = function
  | EqualityHandler lst ->
    EqualityHandler
      (List.map (fun (e1, e2, s, e) -> (Syntax.shift 1 e1, Syntax.shift 1 e2, Syntax.shift 1 s, Syntax.shift 1 e)) lst)
  | BuiltinHandler _ as h -> h

let eval_handler ctx h op k =
  match h with
    | EqualityHandler lst ->
      (match find_handler_case op lst with
        | Some f -> f k
        | None -> Operation (op, k))
    | BuiltinHandler f -> f ctx op k

(** [handle ctx h c] handles computation [c] in context [ctx] using handler [h]. *)
let rec handle ctx h = function
  | Value _ as v -> v
  | Abstraction (x, t, r, k) ->
    ignore (Typing.check_sort ctx t) ;
    let h = shift_handler h in
      (match handle (add_parameter x t ctx) h r with
        | Value v -> k (Lambda (x, t, v))
        | (Operation _ | Abstraction _) as r -> Abstraction (x, t, r, k))
  | Operation (op, k) -> eval_handler ctx h op (fun v -> handle ctx h (k v))

and eval ctx (c, loc) =
  match c with
    | Syntax.Abstraction (x, t, c) ->
      ignore (Typing.check_sort ctx t) ;
      let r = eval (add_parameter x t ctx) c in
        Abstraction (x, t, r, (fun v -> Value v))
    | Syntax.Operation op ->
      Operation (op, (fun v -> Value v))
    | Syntax.Handle (c, h) ->
      let r = eval ctx c in
        handle ctx (EqualityHandler h) r
    | Syntax.Let (x, c1, c2) ->
      let r = eval ctx c1 in
        sequence (fun v ->
          let e, t = Value.to_term ctx v in
          let ctx = add_definition x t e ctx in
            eval ctx c2)
          r

let toplevel ctx c =
  let r = eval ctx c in
    handle ctx (BuiltinHandler top_handler) r

let toplet ctx x c =
  let r = toplevel ctx c in
    match r with
      | Value.Value v -> 
        let e, t = Value.to_term ctx v in
          add_definition x t e ctx
      | _ -> Error.runtime ~loc:(snd c) "does not compute"


