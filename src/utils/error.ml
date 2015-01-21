(** Error reporting *)

type details = Location.t * string * string

let print (loc, err_kind, msg) ppf =
  Print.message ~verbosity:1 "@[<hov 2>%s (%t): %s@]"
    err_kind (Location.print loc) msg

exception Error of details

(** [error ~loc err_kind fmt] raises an [Error] of kind [err_kind] with a
    message [fmt] at a location [loc]. The [kfprintf] magic allows us to
    construct the [fmt] using a format string before raising the exception. *)
let error ~loc err_kind =
  let k _ =
    let msg = Format.flush_str_formatter () in
    raise (Error (loc, err_kind, msg))
  in
  Format.kfprintf k Format.str_formatter

let syntax ?loc:(loc=Location.nowhere) fmt = error ~loc "Syntax error" fmt
let typing ?loc:(loc=Location.nowhere) fmt = error ~loc "Typing error" fmt
let runtime ?loc:(loc=Location.nowhere) fmt = error ~loc "Runtime error" fmt
let fatal ?loc:(loc=Location.nowhere) fmt = error ~loc "Fatal error" fmt
let impossible ?loc:(loc=Location.nowhere) fmt = error ~loc "Impossible" fmt
