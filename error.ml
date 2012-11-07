(** Error reporting. *)

(** Exception [Error (err, msg)] indicates an error of type [err] with
    error message [msg]. *)
exception Error of (string * string)

(** [error err_type msg] raises an error of type [err_type], and a message [msg]. The
    [kfprintf] magic allows one to write [msg] using a format string. *)
let error err_type =
  let k _ =
    let msg = Format.flush_str_formatter () in
      raise (Error (err_type, msg))
  in
    Format.kfprintf k Format.str_formatter

let fatal msg = error "Fatal error" msg
let syntax msg = error "Syntax error" msg
let typing msg = error "Typing error" msg
let runtime msg = error "Normalization error" msg
let exc msg = error "Exception" msg
