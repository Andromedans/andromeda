(** Error reporting *)

(** Exception [Error (err, msg)] indicates an error of type [err] with
    error message [msg]. *)
type t = Location.t * string * string
exception Error of t

(** [error ~loc err_type msg] raises an error of type [err_type], and a message [msg]. The
    [kfprintf] magic allows one to write [msg] using a format string. *)
let error ~loc err_type =
  let k _ =
    let _ = Format.pp_close_box Format.str_formatter () in
    let msg = Format.flush_str_formatter () in
      raise (Error (loc, err_type, msg))
  in
    Format.pp_open_hovbox Format.str_formatter 2;
    Format.fprintf Format.str_formatter "%t: " (Location.print loc);
    Format.kfprintf k Format.str_formatter

let syntax  ?loc:(loc=Location.nowhere) msg = error ~loc "Syntax error" msg
let typing  ?loc:(loc=Location.nowhere) msg = error ~loc "Typing error" msg
let runtime ?loc:(loc=Location.nowhere) msg = error ~loc "Runtime error" msg
let exc     ?loc:(loc=Location.nowhere) msg = error ~loc "Exception" msg
let verify  ?loc:(loc=Location.nowhere) msg = error ~loc "Verification error" msg

(* Varieties of fatal errors *)
let fatal          ?loc:(loc=Location.nowhere) msg = error ~loc "Fatal error" msg
let impossible     ?loc:(loc=Location.nowhere) msg = error ~loc "Impossible" msg
let unimplemented  ?loc:(loc=Location.nowhere) msg = error ~loc "Unimplemented" msg

let print (loc, err_type, msg) = Print.message ~verbosity:1 "%s: @[%s@]" err_type msg
