(** Error reporting. *)


(** Exception [Error (err, msg)] indicates an error of type [err] with
    error message [msg]. *)
exception Error of (Position.t * string * string)

(** [error ~loc err_type msg] raises an error of type [err_type], and a message [msg]. The
    [kfprintf] magic allows one to write [msg] using a format string. *)
let error ~loc err_type =
  let k _ =
    let msg = Format.flush_str_formatter () in
      raise (Error (loc, err_type, msg))
  in
    Format.fprintf Format.str_formatter "%s: " (Position.to_string loc);
    Format.kfprintf k Format.str_formatter

let syntax  ?loc:(loc=Position.nowhere) msg = error ~loc "Syntax error" msg
let typing  ?loc:(loc=Position.nowhere) msg = error ~loc "Typing error" msg
let runtime ?loc:(loc=Position.nowhere) msg = error ~loc "Runtime error" msg
let exc     ?loc:(loc=Position.nowhere) msg = error ~loc "Exception" msg
let verify  ?loc:(loc=Position.nowhere) msg = error ~loc "Verification error" msg

(* Varieties of fatal errors *)
let fatal          ?loc:(loc=Position.nowhere) msg = error ~loc "Fatal error" msg
let impossible     ?loc:(loc=Position.nowhere) msg = error ~loc "Impossible" msg
let unimplemented  ?loc:(loc=Position.nowhere) msg = error ~loc "Unimplemented" msg
