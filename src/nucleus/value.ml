(** Runtime values and results *)

type value =
  | Term of Judgement.term
  | Ty of Judgement.ty
  | Closure of closure
  | Handler of handler
  | Tag of Name.ident * value list

and closure = value -> value result

and 'a result =
  | Return of 'a
  | Operation of string * value * (value -> 'a result)

and handler = {
  handler_val: closure option;
  handler_ops: (string * (value -> value -> value result)) list;
  handler_finally: closure option;
}

(** The monadic bind [bind r f] feeds the result [r : result]
    into function [f : value -> 'a]. *)
let rec bind r f =
  match r with
  | Return v -> f v
  | Operation (op, v, k) -> Operation (op, v, fun x -> (bind (k x) f))

let print_closure xs _ ppf =
  Print.print ~at_level:0 ppf "<function>"

let print_handler xs h ppf =
  Print.print ~at_level:0 ppf "<handler>" (* XXX improve in your spare time *)

let print_tag xs t lst ppf =
  Print.print ~at_level:0 ppf "<must go home>"

let print ?max_level xs v ppf =
  match v with
  | Term e -> Judgement.print_term xs e ppf
  | Ty t -> Judgement.print_ty xs t ppf
  | Closure f -> print_closure xs f ppf
  | Handler h -> print_handler xs h ppf
  | Tag (t, lst) -> print_tag xs t lst ppf

let as_term ~loc = function
  | Term e -> e
  | Ty _ -> Error.runtime ~loc "expected a term but got a type"
  | Closure _ -> Error.runtime ~loc "expected a term but got a function"
  | Handler _ -> Error.runtime ~loc "expected a term but got a handler"
  | Tag _  -> assert false

let as_ty ~loc = function
  | Term _ -> Error.runtime ~loc "expected a type but got a term"
  | Ty t -> t
  | Closure _ -> Error.runtime ~loc "expected a type but got a function"
  | Handler _ -> Error.runtime ~loc "expected a type but got a handler"
  | Tag _  -> assert false

let as_closure ~loc = function
  | Term _ -> Error.runtime ~loc "expected a function but got a term"
  | Ty _ -> Error.runtime ~loc "expected a function but got a type"
  | Closure f -> f
  | Handler _ -> Error.runtime ~loc "expected a function but got a handler"
  | Tag _  -> assert false

let as_handler ~loc = function
  | Term _ -> Error.runtime ~loc "expected a handler but got a term"
  | Ty _ -> Error.runtime ~loc "expected a handler but got a type"
  | Closure _ -> Error.runtime ~loc "expected a handler but got a function"
  | Handler h -> h
  | Tag _  -> assert false

let return x = Return x

let return_term e = Return (Term e)

let return_ty t = Return (Ty t)

let to_value ~loc = function
  | Return v -> v
  | Operation (op, _, _) ->
     Error.runtime ~loc "unhandled operation %t" (Name.print_op op)
