(** Pretty-printing functions *)

let message ~verbosity =
  if verbosity <= !Config.verbosity then
    fun fmt -> Format.eprintf (fmt ^^ "@.")
  else
    Format.ifprintf Format.err_formatter

let warning fmt = message ~verbosity:2 ("Warning: " ^^ fmt)

let debug fmt = message ~verbosity:3 ("Debug: " ^^ fmt)

let print ?(at_level=min_int) ?(max_level=max_int) ppf =
  if at_level <= max_level then
    Format.fprintf ppf
  else
    fun fmt -> Format.fprintf ppf ("(@[" ^^ fmt ^^ "@])")
