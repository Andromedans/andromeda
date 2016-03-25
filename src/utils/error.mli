(** Error reporting

    All internal errors are represented uniformly with a single exception that
    carries additional details such as error kind (syntax, typing, ...), message
    or location.

    Errors are raised through helper functions that take an optional location
    and a message in form of a format string. For example, a typing error can be
    raised by [Error.typing ~loc "Type %t is not a product." (print_ty t)]. *)

type ('a,'b) res =
  | OK of 'a
  | Err of 'b

(** Type of error details. *)
type details

(** Print error details. *)
val print : details -> Format.formatter -> unit

(** Exception representing all possible Andromeda errors. *)
exception Error of details

(** Raise a syntax error - used during lexing, parsing, or desugaring. *)
val syntax : loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

(** Raise an impossible error - used in situations where we are {e almost} sure
    in theory that a certain situation cannot exist and we want to alert the
    user to alert us about its existence. *)
val impossible : loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

