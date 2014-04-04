(** Pretty-printing of Brazilian type theory. *)

(** Printing of messages. *)

let verbosity = ref 2

let message msg_type v =
  if v <= !verbosity then
    begin
      Format.eprintf "%s:@\n@[" msg_type ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let error (loc, err_type, msg) = message (err_type) 1 "%s" msg
let warning msg = message "Warning" 2 msg
let debug msg = message "Debug" 3 msg
let equivalence msg = message "Equivalence" 1 msg

(** Print an term, possibly placing parentheses around it. We always
    print things at a given [at_level]. If the level exceeds the
    maximum allowed level [max_level] then the term should be parenthesized.

    Let us consider an example. When printing nested applications, we should print [App
    (App (a, b), c)] as ["a b c"] and [App(a, App(a, b))] as ["a (b c)"]. So
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

(** Print a sequence of things with the given (optional) separator. *)
let sequence ?(sep="") f lst ppf =
  let rec seq = function
    | [] -> print ppf ""
    | [x] -> print ppf "%t" (f x)
    | x :: xs -> print ppf "%t%s@ " (f x) sep ; seq xs
  in
    seq lst

let universe u = print ~at_level:0 "%s" (Universe.to_string u)

let rec term ?max_level xs e ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
    match e with
      | Syntax.Var k -> print "%s" (List.nth xs k)
      | Syntax.Hint (e1, e2) -> print ~at_level:1 "hint %t in %t" (term ~max_level:1 xs e1) (term ~max_level:0 xs e2)
      | Syntax.Ascribe (e, t) -> print ~at_level:1 "%t :: %t" (term ~max_level:1 xs e) (ty ~max_level:1 xs t)


and ty ?max_level xs t ppf =
  match e with
    | Syntax.Universe u ->
    | Syntax.El (u, e) -> print "El(%t, %t)" (universe u) (term e)
