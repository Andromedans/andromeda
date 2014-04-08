(** Pretty-printing of Brazilian type theory. *)

(** Printing of messages. *)

let verbosity = ref 2
let annotate = ref true

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

(** Optionally print a typing annotation in brackets. *)
let annot ?(prefix="") k ppf =
  if !annotate then
    Format.fprintf ppf "%s[@[%t@]]" prefix k
  else
    Format.fprintf ppf ""

(** Print a sequence of things with the given (optional) separator. *)
let sequence ?(sep="") f lst ppf =
  let rec seq = function
    | [] -> print ppf ""
    | [x] -> print ppf "%t" (f x)
    | x :: xs -> print ppf "%t%s@ " (f x) sep ; seq xs
  in
    seq lst

let universe (u,_) ppf =
  print ~at_level:0 ppf "%s" (Universe.to_string u)

let rec term ?max_level xs (e,_) ppf =
  let print' = print
  and print ?at_level = print ?max_level ?at_level ppf in
    match e with

      | Syntax.Var k ->
        print ~at_level:0 "%s" (List.nth xs k)

      | Syntax.Equation (e1, e2) ->
        print ~at_level:4 "equation %t in %t"
          (term ~max_level:3 xs e1)
          (term ~max_level:4 xs e2)

      | Syntax.Rewrite (e1, e2) ->
        print ~at_level:4 "rewrite %t in %t"
          (term ~max_level:3 xs e1)
          (term ~max_level:4 xs e2)

      | Syntax.Ascribe (e, t) ->
        print ~at_level:4 "%t :: %t"
          (term ~max_level:3 xs e)
          (ty ~max_level:4 xs t)

      | Syntax.Lambda (x, t, u, e) ->
        print ~at_level:4 "fun (%s : %t) =>%t %t"
          x
          (ty ~max_level:4 xs t)
          (annot (ty ~max_level:4 (x::xs) u))
          (term ~max_level:4 (x::xs) e)

      | Syntax.App ((x, t, u), e1, e2) ->
        print ~at_level:1 "%t%t %t"
          (term ~max_level:1 xs e1)
          (annot ~prefix:" @"
             (fun ppf -> print' ~max_level:4 ppf "%s : %t . %t" x (ty ~max_level:4 xs t) (ty ~max_level:4 (x::xs) u)))
          (term ~max_level:0 xs e2)

      | Syntax.UnitTerm -> print ~at_level:0 "()"

      | Syntax.Idpath (t, e) -> print ~at_level:0 "idpath%t %t"
        (annot (ty ~max_level:4 xs t))
        (term ~max_level:0 xs e)

      | Syntax.J (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
        print ~at_level:1 "J (%t, [%s %s %s . %t], [%s . %t], %t, %t, %t)"
          (ty ~max_level:4 xs t)
          x y p (ty ~max_level:4 (x::y::p::xs) u)
          z (term ~max_level:4 (z::xs) e1)
          (term ~max_level:4 xs e2)
          (term ~max_level:4 xs e3)
          (term ~max_level:4 xs e4)

      | Syntax.Refl (t, e) ->
        print ~at_level:0 "refl%t %t"
          (annot (ty ~max_level:4 xs t))
          (term ~max_level:0 xs e)

      | Syntax.Coerce (u1, u2, e) ->
        print ~at_level:1 "coerce (%t, %t, %t)"
          (universe u1)
          (universe u2)
          (term ~max_level:4 xs e)

      | Syntax.NameUnit -> print ~at_level:0 "unit"

      | Syntax.NameProd (x, e1, e2) ->
        print ~at_level:3 "(%s : %t) -> %t"
          x 
          (term ~max_level:4 xs e1)
          (term ~max_level:3 (x::xs) e2)

      | Syntax.NameUniverse u ->
        print ~at_level:1 "Universe %t"
          (universe u)

      | Syntax.NamePaths (e1, e2, e3) ->
        print ~at_level:2 "%t =%t %t"
          (term ~max_level:1 xs e2)
          (annot (term ~max_level:4 xs e1))
          (term ~max_level:1 xs e3) 

      | Syntax.NameId (e1, e2, e3) ->
        print ~at_level:2 "%t ==%t %t"
          (term ~max_level:1 xs e2)
          (annot (term ~max_level:4 xs e1))
          (term ~max_level:1 xs e3)

and ty ?max_level xs (t,_) ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
    match t with

      | Syntax.Universe u ->
        print ~at_level:1 "Universe %t"
          (universe u)

      | Syntax.El e ->
        print "%t"
          (term ?max_level xs e)

      | Syntax.Unit ->
        print ~at_level:0 "unit"

      | Syntax.Prod (x, t1, t2) ->
        print ~at_level:3 "(%s : %t) -> %t"
          x
          (ty ~max_level:4 xs t1)
          (ty ~max_level:3 (x::xs) t2)

      | Syntax.Paths (t, e1, e2) ->
        print ~at_level:2 "%t =%t %t"
          (term ~max_level:1 xs e1)
          (annot (ty ~max_level:4 xs t))
          (term ~max_level:1 xs e2)

      | Syntax.Id (t, e1, e2) ->
        print ~at_level:2 "%t ==%t %t"
          (term ~max_level:1 xs e1)
          (annot (ty ~max_level:4 xs t))
          (term ~max_level:1 xs e2)
