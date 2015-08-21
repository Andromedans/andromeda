(** Runtime values and results *)

type value =
  | Judge of Tt.term * Tt.ty (** A judgement [e : t] where [e] is guaranteed to have the type [t]. *)
  | Closure of closure

(** A closure *)
and closure = value -> result

(** Possible results of evaluating a computation. *)
and result =
  | Return of value
  | Operation of string * value * closure

(** NB: This is an effectful computation. *)
let fresh ~loc x t =
  let y = Name.fresh x in
    y, Judge (Tt.mk_name ~loc y, t)

(** The monadic bind [bind r f] feeds the result [r : result]
    into function [f : value -> 'a]. *)
let rec bind r f =
  match r with
  | Return v -> f v
  | Operation (op, v, k) -> Operation (op, v, fun x -> (bind (k x) f))

let print_judge ?max_level xs (e,t) ppf =
  Print.print ~at_level:0 ppf "@[<hov 2>%t@\n    : %t@]"
              (Tt.print_term ~max_level:999 xs e)
              (Tt.print_ty ~max_level:999 xs t)

let print_closure ?max_level xs _ ppf =
  Print.print ~at_level:0 ppf "<function>"

let print ?max_level xs v ppf =
  match v with
  | Judge (e, t) -> print_judge ?max_level xs (e, t) ppf
  | Closure f -> print_closure ?max_level xs f ppf

let as_judge ~loc = function
  | Judge (e, t) -> (e, t)
  | Closure _ -> Error.runtime ~loc "expected a judgment but got a function"

let as_closure ~loc = function
  | Judge (e,t) -> Error.runtime ~loc "expected a function but got a judgement %t" (print_judge [] (e,t))
  | Closure f -> f

let return_judge e t = Return (Judge (e, t))

let to_value ~loc = function
  | Return v -> v
  | Operation (op, _, _) ->
     Error.runtime ~loc "unhandled operation %t" (Name.print_op op)
