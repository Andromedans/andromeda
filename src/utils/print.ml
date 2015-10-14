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

let rec sequence print_u separator us ppf =
  match us with
  | [] -> print ppf ""
  | [u] -> print ppf "@[%t@]" (print_u u)
  | u :: us ->
    print ppf "%t%s@ %t"
      (print_u u)
      separator
      (sequence print_u separator us)

(** Unicode and ascii version of symbols *)

let char_lambda () = if !Config.ascii then "fun" else "λ"
let char_arrow ()  = if !Config.ascii then "->" else "→"
let char_darrow () = if !Config.ascii then "=>" else "⇒"
let char_prod ()   = if !Config.ascii then "forall" else "Π"
let char_equal ()  = if !Config.ascii then "==" else "≡"
let char_vdash ()  = if !Config.ascii then "|-" else "⊢"

