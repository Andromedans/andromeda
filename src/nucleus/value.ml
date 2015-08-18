(** Runtime values and results *)

type value =
(** A value is obtained by successfully evaluating a computation. *)
  Tt.term * Tt.ty
  (** A judgement [e : t] where [e] is guaranteed to have the type [t]. *)

(** A continuation *)
type cont = value -> result

(** Possible results of evaluating a computation. *)
and result =
  | Return of value
  | Operation of string * value * cont

let print ?max_level xs v ppf =
  let (e,t) = v in
    Print.print ~at_level:0 ppf "@[<hov 2>%t@\n    : %t@]"
          (Tt.print_term ~max_level:999 xs e)
          (Tt.print_ty ~max_level:999 xs t)

let to_value ~loc = function
  | Return v -> v
  | Operation (op, _, _) ->
     Error.runtime ~loc "unhandled operation %t" (Name.print_op op)
