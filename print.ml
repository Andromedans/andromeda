let fprintf = Format.fprintf

let print ?(max_level=9999) ?(at_level=0) ppf =
  if max_level < at_level then
    begin
      Format.fprintf ppf "(@[";
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@])") ppf
    end
  else
    begin
      Format.fprintf ppf "@[";
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]") ppf
    end

let variable x ppf =
  match x with
    | Syntax.Dummy -> print ppf "_"
    | Syntax.String x -> print ppf "%s" x
    | Syntax.Gensym (x, k) -> print ppf "%s_%d" x k

let rec expr t ppf =
  let rec expr ?max_level t ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      match t with
        | Syntax.Var x -> variable x ppf
        | Syntax.Universe k -> print ~at_level:5 "Type %d" k
        | Syntax.Pi (Syntax.Dummy, t1, t2) -> print "%t -> %t" (expr t1) (expr t2)
        | Syntax.Pi (x, t1, t2) -> print "forall %t : %t, %t" (variable x) (expr t1) (expr t2)
        | Syntax.Lambda (x, t, e) -> print "fun %t : %t => %t" (variable x) (expr t) (expr e)
        | Syntax.App (e1, e2) -> print ~at_level:1 "%t %t" (expr e1) (expr ~max_level:0 e2)
  in
    expr t ppf
  
let verbosity = ref 3
let message msg_type v =
  if v <= !verbosity then
    begin
      Format.eprintf "@[%s: " msg_type;
      Format.kfprintf (fun ppf -> fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let error (err_type, msg) = message (err_type) 1 "%s" msg
let check msg = message "Check" 2 msg
let warning msg = message "Warning" 3 msg
let debug msg = message "Debug" 4 msg
