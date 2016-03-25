(** Error reporting *)

type ('a,'b) res =
  | OK of 'a
  | Err of 'b

type details = Location.t * string * string

let print (loc, err_kind, msg) ppf =
  Format.fprintf ppf "%t: %s\n%s"
    (Location.print loc) err_kind msg

exception Error of details

(** [error ~loc err_kind fmt] raises an [Error] of kind [err_kind] with a
    message [fmt] at a location [loc]. The [kfprintf] magic allows us to
    construct the [fmt] using a format string before raising the exception. *)
let error ~loc err_kind =
  let k _ =
    let msg = Format.flush_str_formatter () in
    raise (Error (loc, err_kind, msg))
  in
  fun fmt -> Format.kfprintf k Format.str_formatter ("  @[" ^^ fmt ^^ "@]")

let syntax ~loc fmt = error ~loc "Syntax error" fmt
let impossible ~loc fmt =
  let message_header =
    format_of_string
      "####################################################################@\n\
       # SOMETHING THAT SHOULD NEVER HAPPEN JUST HAPPENED. TO GET A BEER, #@\n\
       # PLEASE REPORT THE FOLLOWING ERROR MESSAGE TO THE DEVELOPERS AND  #@\n\
       # EXPLAIN WHAT YOU WERE DOING BEFORE THE ERROR OCCURRED.           #@\n\
       ####################################################################@\n"
  in
  error ~loc "Impossible error" (message_header ^^ fmt)

