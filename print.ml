(** Pretty-printing of expressions with the Ocaml [Format] library. *)

(** Print an expression, possibly placing parentheses around it. We always
    print things at a given "level" [at_level]. If the level exceeds the
    maximum allowed level [max_level] then the expression should be parenthesized.

    Let us consider an example. When printing nested applications, we should print [App
    (App (e1, e2), e3)] as ["e1 e2 e3"] and [App(e1, App(e2, e3))] as ["e1 (e2 e3)"]. So
    if we assign level 1 to applications, then during printing of [App (e1, e2)] we should
    print [e1] at [max_level] 1 and [e2] at [max_level] 0.
*)
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

(** Print the name of a variable. *)
let variable x ppf =
  match x with
    | Syntax.Dummy -> print ppf "_"
    | Syntax.String x -> print ppf "%s" x
    | Syntax.Gensym (x, k) -> print ppf "%s_%d" x k

(** [expr e ppf] prints (beautified) expression [e] using formatter [ppf]. *)
let expr e ppf =
  let rec expr ?max_level (e, _) ppf =  expr'?max_level e ppf
  and expr' ?max_level e ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      match e with
        | Syntax.Var x -> variable x ppf
        | Syntax.Universe k -> print "Type %d" k
        | Syntax.Pi (Syntax.Dummy, t1, t2) -> print ~at_level:3 "%t ->@;%t" (expr ~max_level:2 t1) (expr t2)
        | Syntax.Pi (x, t1, t2) -> print ~at_level:3 "forall %t : %t,@;%t" (variable x) (expr ~max_level:4 t1) (expr t2)
        | Syntax.Lambda (x, t, e) -> print ~at_level:3 "fun %t : %t =>@;%t" (variable x) (expr t) (expr e)
        | Syntax.App (e1, e2) -> print ~at_level:1 "%t@;%t" (expr ~max_level:1 e1) (expr ~max_level:0 e2)
  in
    expr (Beautify.beautify e) ppf
    
let expr' e ppf = expr (Syntax.nowhere e) ppf
  
(** Support for printing of errors, warning and debugging information. *)
let verbosity = ref 3
let message msg_type v =
  if v <= !verbosity then
    begin
      Format.eprintf "@[%s: " msg_type;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let error (err_type, msg) = message (err_type) 1 "%s" msg
let warning msg = message "Warning" 2 msg
let debug msg = message "Debug" 3 msg
