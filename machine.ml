(** Abstract machine for evaluating computations. *)

open Context
open Value

(*
let run_operation ctx (op, loc) =
  match op with
    | Syntax.Inhabit t ->
      ignore (Typing.check_sort ctx t) ;
      Error.runtime ~loc "sorry, this has not been implemented yet" (Print.expr ctx.names t)
    | Syntax.Infer e ->
      let t = Typing.infer ctx e in
        mk_tywtn e t, mk_tyjdg e t
    | Syntax.HasType (e, t) ->
      Typing.check ctx e t ;
      mk_tywtn e t, mk_tyjdg e t
    | Syntax.Equal (e1, e2, t) ->
      ignore (Typing.check_sort ctx t) ;
      if Typing.equal_at ctx e1 e2 t
      then mk_eqwtn e1 e2 t, mk_eqjdg e1 e2 t
      else Error.runtime ~loc "do not know how to derive %t" (Print.expr ctx.names (mk_eqjdg e1 e2 t))
*)

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

let shift_handler_case (e1, e2, s, e) =
  (Syntax.shift 1 e1, Syntax.shift 1 e2, Syntax.shift 1 s, Syntax.shift 1 e)

let rec eval_handler ctx lst =
  let rec h = function
    | Value _ as v -> v
    | Abstraction (x, t, r, k) ->
      let lst = List.map shift_handler_case lst in
        (match eval_handler (add_parameter x t ctx) lst r with
          | Value v -> k (Lambda (x, t, v))
          | (Operation _ | Abstraction _) as r -> Abstraction (x, t, r, k))
    | Operation (op, k) ->
      let k' u = h (k u) in
        (match find_handler_case op lst with
          | Some f -> f k'
          | None -> Operation (op, k'))
  in
    h

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
      let h = eval_handler ctx h in
        h r
