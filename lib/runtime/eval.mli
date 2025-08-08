(** Evaluation of computations *)

val toplevel :
  quiet:bool ->
  print_annot:(unit -> Mlty.ty_schema -> Format.formatter -> unit) ->
  Syntax.toplevel -> unit Runtime.toplevel

val toplevels :
  quiet:bool ->
  print_annot:(unit -> Mlty.ty_schema -> Format.formatter -> unit) ->
  Syntax.toplevel list -> unit Runtime.toplevel
