(** Pretty-printing functions *)

let message ~verbosity =
  if verbosity <= !Config.verbosity then
    fun fmt -> Format.eprintf (fmt ^^ "@.")
  else
    Format.ifprintf Format.err_formatter

let warning fmt = message ~verbosity:2 ("Warning: " ^^ fmt)

let debug fmt = message ~verbosity:3 ("Debug: " ^^ fmt)

let print ?(max_level=max_int) ?(at_level=0) ppf =
  if max_level < at_level then
    fun fmt -> Format.fprintf ppf ("(@[" ^^ fmt ^^ "@])")
  else
    Format.fprintf ppf
