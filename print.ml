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

(** Print a sequence of things with the given (optional) separator. *)
let sequence ?(sep="") f lst ppf =
  let rec seq = function
    | [] -> print ppf ""
    | [x] -> print ppf "%t" (f x)
    | x :: xs -> print ppf "%t%s@ " (f x) sep ; seq xs
  in
    seq lst

(** [tpi xs a ppf] prints abstraction [a] as dependent product using formatter [ppf]. *)
let rec tpi ?max_level xs x (t1:Syntax.ty) (t2:Syntax.ty) ppf =
  if Syntax.occursTy 0 t2
  then
    let x = Beautify.refresh x xs in
      print ~at_level:3 ppf "forall %s :@ %t,@ %t" x (ty ~max_level:2 xs t1) (ty (x :: xs) t2)
  else
    print ~at_level:3 ppf "%t ->@ %t" (ty ~max_level:2 xs t1) (ty ("_" :: xs) t2)

(** [kpi xs x t1 k2 ppf] prints abstraction  as dependent product using formatter [ppf]. *)
and kpi ?max_level xs x t1 k2 ppf =
  if Syntax.occursKind 0 k2
  then
    let x = Beautify.refresh x xs in
      print ~at_level:3 ppf "forall %s :@ %t,@ %t" x (ty ~max_level:2 xs t1) (kind (x :: xs) k2)
  else
    print ~at_level:3 ppf "%t ->@ %t" (ty ~max_level:2 xs t1) (kind ("_" :: xs) k2)

(** [lambda xs x t e ppf] prints function [fun x => e] using formatter [ppf]. *)
and lambda xs x (t : Syntax.ty) e ppf =
  let x =
    if Syntax.occurs 0 e
    then Beautify.refresh x xs
    else "_"
  in
    print ~at_level:3 ppf "fun %s : %t =>@ %t" x (ty ~max_level:2 xs t) (expr (x :: xs) e)

(** [expr ctx e ppf] prints expression [e] using formatter [ppf]. *)
and expr ?max_level xs e ppf =
  let rec expr ?max_level xs e ppf = expr' ?max_level xs e ppf
  and expr' ?max_level xs e ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      if not (Format.over_max_boxes ()) then
        match e with
          | Syntax.Var k -> print "%s" (List.nth xs k)
          | Syntax.Lambda (x, t, e) -> print ~at_level:3 "%t" (lambda xs x t e)
          | Syntax.App (e1, e2) -> print ~at_level:1 "%t@ %t" (expr ~max_level:1 xs e1) (expr ~max_level:0 xs e2)
          (*
          | Syntax.Operation (tag, exps) -> print ppf "[%t %a]" (operation ?max_level xs op)
                                              (sequence ~sep:" " (expr
                                              ~max_level:1 xs) exps)
          | Syntax.Handle (c, h) -> print ppf "handle %t with <handler>" (computation xs c)
          *)
  in
    expr ?max_level xs e ppf

(** [ty ctx t ppf] prints type [t] using formatter [ppf]. *)
and ty ?max_level xs t ppf =
  let rec ty ?max_level xs t ppf = ty' ?max_level xs t ppf
  and ty' ?max_level xs t ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      if not (Format.over_max_boxes ()) then
        match t with
          | Syntax.TVar k -> print "%s" (List.nth xs k)
          | Syntax.TPi (x, t1, t2) -> print ~at_level:3 "%t" (tpi xs x t1 t2)
          | Syntax.TApp (t1, e2) -> print ~at_level:1 "%t@ %t" (ty ~max_level:1 xs t1) (expr ~max_level:0 xs e2)
  in
    ty ?max_level xs t ppf

(** [kind ctx k ppf] prints kind [k] using formatter [ppf]. *)
and kind ?max_level xs k ppf =
  let rec kind ?max_level xs k ppf = kind' ?max_level xs k ppf
  and kind' ?max_level xs k ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      if not (Format.over_max_boxes ()) then
        match k with
          | Syntax.KType -> print "Type"
          | Syntax.KPi (x, t1, k2) -> print ~at_level:3 "%t" (kpi xs x t1 k2)
  in
    kind ?max_level xs k ppf


    (*
let operation ?max_level xs op ppf =
  match op with
    | Syntax.Inhabit t -> print ppf "[ ? :: %t ]" (expr ~max_level:2 xs t)

let rec computation ?max_level xs c ppf =
  match c with
    | Syntax.Return e -> print ppf "return %t" (expr ~max_level:4 xs e)
    | Syntax.Abstraction  (x, t, c) -> print ppf "fun %s : %t => %t" x (expr ~max_level:2 xs t) (computation (x::xs) c)
    | Syntax.Operation op -> print ppf "%t" (operation ?max_level xs op)
    | Syntax.Handle (c, h) -> print ppf "handle %t with <handler>" (computation xs c)
    | Syntax.Let (x, c1, c2) -> print ~at_level:3 ppf "let x := %t in %t" (computation ~max_level:2 xs c1) (computation (x::xs) c2)

let rec value ?max_level xs v ppf =
  match v with
    | Value.Lambda (x, t, v) -> print ppf "forall %s : %t, %t" x (expr ~max_level:2 xs t) (value (x::xs) v)

let rec result ?max_level xs r ppf =
  match r with
    | Value.Value v -> print ppf "%t" (value xs v)
    | Value.Operation (op, _) -> print ppf "%t ..." (operation xs op)
    | Value.Abstraction (x, t, r, _) ->
      print ppf "fun %s : %t => %t ..." x (expr ~max_level:2 xs t) (result (x::xs) r)
    | Value.Definition (x, t, e, r, _) ->
      print ppf "let %s := %t : %t in %t ..." x (expr ~max_level:2 xs e) (expr ~max_level:2 xs t) (result (x::xs) r)
*)

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

