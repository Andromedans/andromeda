(** Pretty-printing functions *)

let message msg_type v =
  if v <= !Config.verbosity then
    begin
      Format.eprintf "%s: @[" msg_type ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let warning msg = message "Warning" 2 msg
let debug msg = message "Debug" 3 msg

let print ?(max_level=9999) ?(at_level=0) ppf =
  if max_level < at_level then
    begin
      Format.fprintf ppf "(@[" ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@])") ppf
    end
  else
    begin
      Format.fprintf ppf
    end

let sequence ?(sep=" ") f lst ppf =
  let rec seq = function
    | [] -> print ppf ""
    | [x] -> print ppf "%t" (f x)
    | x :: xs -> print ppf "%t%s@," (f x) sep ; seq xs
  in
    seq lst
