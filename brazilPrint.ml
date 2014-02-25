(** Pretty-printing of termessions with the Ocaml [Format] library. *)

module S = BrazilSyntax

(** Print an term, possibly placing parentheses around it. We always
    print things at a given "level" [at_level]. If the level exceeds the
    maximum allowed level [max_level] then the term should be parenthesized.

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

(** Print a sequence of things with the given (optional) separator. *)
let sequence ?(sep="") f lst ppf =
  let rec seq = function
    | [] -> print ppf ""
    | [x] -> print ppf "%t" (f x)
    | x :: xs -> print ppf "%t%s@ " (f x) sep ; seq xs
  in
    seq lst

(** [tpi xs a ppf] prints abstraction [a] as dependent product using formatter [ppf]. *)
let rec pi ?max_level xs x t1 t2 ppf =
  if S.occurs 0 t2 then
    let x = Beautify.refresh x xs in
      print ~at_level:3 ppf "(%s :@ %t) ->@ %t"
             x (term ~max_level:2 xs t1) (term (x :: xs) t2)
  else
    print ~at_level:3 ppf "%t ->@ %t" (term ~max_level:2 xs t1) (term ("_" :: xs) t2)

(** [tpi xs a ppf] prints abstraction [a] as dependent product using formatter [ppf]. *)
and sigma ?max_level xs x t1 t2 ppf =
  if S.occurs 0 t2 then
    let x = Beautify.refresh x xs in
      print ~at_level:3 ppf "(%s :@ %t) *@ %t"
             x (term ~max_level:2 xs t1) (term (x :: xs) t2)
  else
    print ~at_level:3 ppf "%t *@ %t"
      (term ~max_level:2 xs t1) (term ~max_level:2 ("_" :: xs) t2)

(** [lambda xs x t e ppf] prints function [fun x => e] using formatter [ppf]. *)
and lambda xs x t e ppf =
  let x =
    if S.occurs 0 e
    then Beautify.refresh x xs
    else "_"
  in
    print ~at_level:3 ppf "fun %s : %t =>@ %t" x (term ~max_level:2 xs t) (term (x :: xs) e)

(** [term ctx e ppf] prints termession [e] using formatter [ppf]. *)
  and term ?max_level xs e ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      if not (Format.over_max_boxes ()) then
        match e with
          | S.Var k -> print "%s" (List.nth xs k)
          | S.Lambda (x, t, e) -> print ~at_level:3 "%t" (lambda xs x t e)
          | S.App (e1, e2) -> print ~at_level:1 "%t@ %t" (term ~max_level:1 xs e1) (term ~max_level:0 xs e2)
          | S.Pair (e1, e2) -> print ~at_level:0 "(%t,@ %t)" (term ~max_level:1 xs e1) (term ~max_level:0 xs e2)
          | S.Proj (1, e2) -> print ~at_level:1 "%t.fst" (term ~max_level:0 xs e2)
          | S.Proj (2, e2) -> print ~at_level:1 "%t.snd" (term ~max_level:0 xs e2)
          | S.Proj (i1, e2) -> print ~at_level:1 "%t.%d"
               (term ~max_level:0 xs e2) i1
          | S.Pi (x, t1, t2) -> print ~at_level:3 "%t" (pi xs x t1 t2)
          | S.Sigma (x, t1, t2) -> print ~at_level:3 "%t" (sigma xs x t1 t2)
          | S.Refl (S.Ju, e, t) -> print ~at_level:1 "Refl[%t](%t)"
               (term ~max_level:3 xs t) (term ~max_level:3 xs e)
          | S.Refl (S.Pr, e, t) -> print ~at_level:1 "refl[%t](%t)"
               (term ~max_level:3 xs t) (term ~max_level:3 xs e)
          | S.Eq(o,e1, e2, t) ->
              print "(%t %s %t @@ %t)"
              (term ~max_level:1 xs e1)
              (match o with S.Pr -> "=" | S.Ju -> "==")
              (term ~max_level:1 xs e2)
              (term ~max_level:1 xs t)
          | S.J(o, q, w, a, b, t, p) ->
              print "%s(%t, %t, %t, %t, %t, %t)"
              (match o with S.Pr -> "j" | S.Ju -> "J")
              (term ~max_level:3 xs q)
              (term ~max_level:3 xs w)
              (term ~max_level:3 xs a)
              (term ~max_level:3 xs b)
              (term ~max_level:3 xs t)
              (term ~max_level:3 xs p)
          | S.U (S.Type i) -> print "Type(%d)" i
          | S.U (S.Fib i)  -> print "type(%d)" i
          | S.Base (S.TUnit) -> print "unit"
          | S.Const (S.Unit) -> print "()"

    (** Support for printing of errors, warning and debugging information. *)

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

