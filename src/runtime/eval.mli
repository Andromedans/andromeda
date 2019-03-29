(** Evaluation of computations *)

val toplevel :
  quiet:bool ->
  print_annot:(unit -> Mlty.ty_schema -> Format.formatter -> unit) ->
  Rsyntax.toplevel -> unit Runtime.toplevel

val toplevels :
  quiet:bool ->
  print_annot:(unit -> Mlty.ty_schema -> Format.formatter -> unit) ->
  Rsyntax.toplevel list -> unit Runtime.toplevel
