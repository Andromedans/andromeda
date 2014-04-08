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

(** Optionally print a typing annotation in brackets. *)
let annot ?(prefix="") ppf =
  if !annotate then
    begin
      Format.kprintf ppf "%s[@[" prefix ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]]") ppf
    end
  else
    Format.ikprintf ppf

(** Print a sequence of things with the given (optional) separator. *)
let sequence ?(sep="") f lst ppf =
  let rec seq = function
    | [] -> print ppf ""
    | [x] -> print ppf "%t" (f x)
    | x :: xs -> print ppf "%t%s@ " (f x) sep ; seq xs
  in
    seq lst

let universe u ppf =
  print ~at_level:0 ppf "%s" (Universe.to_string u)

let rec term ?max_level xs e ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
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
          (ty ~max_level:4 t)
          (annot ppf "%t" (ty ~max_level:4 (x::xs) u))
          (term ~max_level:4 (x::xs) e)

      | Syntax.App ((x, t, u), e1, e2) ->
        print ~at_level:1 "%t%t %t"
          (term ~max_level:1 xs e1)
          (annot ppf ~prefix:" @" "%s : %t . %t" x (ty ~max_level:4 xs t) (ty ~max_level:4 (x:xs) u))
          (term ~max_level:0 xs e2)

      | Syntax.UnitTerm -> print ~at_level:0 "()"

      | Syntax.Idath (t, e) -> print ~at_level:0 "idpath%t %t"
        (annot ppf "%t" (ty ~max_level:4 xs u))
        (term ~max_level:0 xs e)

      | Syntax.J (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
        print

      | Syntax.Refl (t, e) ->
        print ~at_level:0 "refl%t %t"
          (annot ppf "%t" (ty ~max_level:4 xs u))
          (term ~max_level:0 xs e)

      | Syntax.Coerce (u1, u2, e) ->
        print ~at_level:1 "coerce (%t, %t, %t)"
          (universe u1)
          (universe u2)
          (term ~max_level:4 xs e)

      | Syntax.NameProd (x, e1, e2) ->
        print ~at_level:3 "(%s : %t) -> %t"
          x 
          (ty xs t1)
          (ty ~max_level:3 (x::xs) t2)

      | Syntax.NameUniverse u ->
        print ~at_level:1 "Universe %t"
          (universe u)

      | Syntax.NamePaths (e1, e2, e3) ->
        print ~at_level:2 "%t =%t %t"
          (term ~max_level:1 e2)
          (annot ppf "%t" (term ~max_level:4 xs e1))
          (term ~max_level:1 e3) 

      | Syntax.NameId (e1, e2, e3) ->
        print ~at_level:2 "%t == %t @ %t"
          (term ~max_level:1 e2)
          (annot ppf (term ~max_level:4 xs e1))
          (term ~max_level:1 e3)

and ty ?max_level xs t ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
    match e with

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
          (annot ppf "%t" (ty ~max_level:4 xs t))
          (term ~max_level:1 xs e2)

      | Syntax.Id (t, e1, e2) ->
        print ~at_level:2 "%t ==%t %t"
          (term ~max_level:1 xs e1)
          (annot ppf "%t" (ty ~max_level:4 xs t))
          (term ~max_level:1 xs e2)
