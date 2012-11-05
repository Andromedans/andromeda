let fprintf = Format.fprintf

let print ?(max_level=9999) ?(at_level=0) ppf =
  if max_level < at_level then
    begin
      Format.fprintf ppf "(@[" ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@])") ppf
    end
  else
    begin
      Format.fprintf ppf "@[" ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]") ppf
    end

let variable x ppf =
  match x with
    | Concrete.Dummy -> print ppf "_"
    | Concrete.String x -> print ppf "%s" x
    | Concrete.Gensym (x, k) -> print ppf "%s_%d" x k

let expr e ppf =
  let e = Syntax.uneval e in
  let rec expr ?max_level e ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      match e with
        | Concrete.Var x -> variable x ppf
        | Concrete.Universe k -> print "Type %d" k
        | Concrete.Pi (Concrete.Dummy, t1, t2) -> print ~at_level:3 "%t ->@;%t" (expr ~max_level:2 t1) (expr t2)
        | Concrete.Pi (x, t1, t2) -> print ~at_level:3 "forall %t : %t,@;%t" (variable x) (expr ~max_level:4 t1) (expr t2)
        | Concrete.Lambda (x, t, e) -> print ~at_level:3 "fun %t : %t =>@;%t" (variable x) (expr t) (expr e)
        | Concrete.App (e1, e2) -> print ~at_level:1 "%t %t" (expr ~max_level:1 e1) (expr ~max_level:0 e2)
  in
    expr (Concrete.beautify e) ppf
      
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
