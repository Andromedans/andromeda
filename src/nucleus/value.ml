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

let rec print_tag ?max_level xs t lst ppf =
  match lst with
  | [] -> Print.print ?max_level ~at_level:0 ppf "'%t" (Name.print_ident t)
  | (_::_) -> Print.print ?max_level ~at_level:1 ppf "'%t %t"
                          (Name.print_ident t)
                          (Print.sequence (print_value ~max_level:0 xs) "" lst)

and print_value ?max_level xs v ppf =
  match v with
  | Term e -> Judgement.print_term ?max_level xs e ppf
  | Ty t -> Judgement.print_ty ?max_level xs t ppf
  | Closure f -> print_closure xs f ppf
  | Handler h -> print_handler xs h ppf
  | Tag (t, lst) -> print_tag ?max_level xs t lst ppf

let as_term ~loc = function
  | Term e -> e
  | Ty _ -> Error.runtime ~loc "expected a term but got a type"
  | Closure _ -> Error.runtime ~loc "expected a term but got a function"
  | Handler _ -> Error.runtime ~loc "expected a term but got a handler"
  | Tag _  -> Error.runtime ~loc "expected a term but got a tag"

let as_ty ~loc = function
  | Term _ -> Error.runtime ~loc "expected a type but got a term"
  | Ty t -> t
  | Closure _ -> Error.runtime ~loc "expected a type but got a function"
  | Handler _ -> Error.runtime ~loc "expected a type but got a handler"
  | Tag _  -> Error.runtime ~loc "expected a type but got a tag"

let as_closure ~loc = function
  | Term _ -> Error.runtime ~loc "expected a function but got a term"
  | Ty _ -> Error.runtime ~loc "expected a function but got a type"
  | Closure f -> f
  | Handler _ -> Error.runtime ~loc "expected a function but got a handler"
  | Tag _  -> Error.runtime ~loc "expected a function but got a tag"

let as_handler ~loc = function
  | Term _ -> Error.runtime ~loc "expected a handler but got a term"
  | Ty _ -> Error.runtime ~loc "expected a handler but got a type"
  | Closure _ -> Error.runtime ~loc "expected a handler but got a function"
  | Handler h -> h
  | Tag _  -> Error.runtime ~loc "expected a handler but got a tag"

let return x = Return x

let return_term e = Return (Term e)

let return_ty t = Return (Ty t)

let to_value ~loc = function
  | Return v -> v
  | Operation (op, _, _) ->
     Error.runtime ~loc "unhandled operation %t" (Name.print_op op)

let rec equal_value v1 v2 =
  match v1, v2 with
    | Term (_,te1,_), Term (_,te2,_) ->
      Tt.alpha_equal te1 te2

    | Ty (_,t1), Ty (_,t2) ->
      Tt.alpha_equal_ty t1 t2

    | Tag (t1,vs1), Tag (t2,vs2) ->
      Name.eq_ident t1 t2 &&
      let rec fold vs1 vs2 =
        match vs1, vs2 with
          | [], [] -> true
          | v1::vs1, v2::vs2 ->
            equal_value v1 v2 &&
            fold vs1 vs2
          | _::_, [] | [], _::_ -> false
        in
      fold vs1 vs2

    | Term _, (Ty _ | Closure _ | Handler _ | Tag _)
    | Ty _, (Term _ | Closure _ | Handler _ | Tag _)
    | Closure _, (Term _ | Ty _ | Handler _ | Tag _)
    | Handler _, (Term _ | Ty _ | Closure _ | Tag _)
    | Tag _, (Term _ | Ty _ | Closure _ | Handler _) ->
      false

    | Closure _, Closure _
    | Handler _, Handler _ ->
      false

