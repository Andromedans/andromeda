(** Evaluation of computations *)

type error

exception Error of error Location.located

val print_error : error -> Format.formatter -> unit

val toplevel :
  quiet:bool ->
  print_annot:(unit -> Rsyntax.ml_schema -> Format.formatter -> unit) ->
  Rsyntax.toplevel -> unit Runtime.toplevel
