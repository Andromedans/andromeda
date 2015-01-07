(** Pretty-printing of Andromedan type theory. *)

(** Printing of messages. *)

let verbosity = ref 4
let annotate = ref false
let displayable = ref ["all"]

let message msg_type v =
  if v <= !verbosity then
    begin
      Format.eprintf "%s: @[" msg_type ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let error (loc, err_type, msg) = message (err_type) 1 "%s" msg
let warning msg = message "Warning" 2 msg
let debug ?(category="all") msg =
  if List.mem category (!displayable) then
    message "Debug" 3 msg
  else
    message "Dummy" (!verbosity + 1) msg

(** Print a term, possibly placing parentheses around it. We always
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

let name x ppf = print ~at_level:0 ppf "%s" (Common.to_string x)

let rec binder ctx (x, t) ppf =
  print ppf "(%t : %t)"
        (name x)
        (ty ctx t)

(** [prod ctx ts t ppf] prints a dependent product using formatter [ppf]. *)
and prod ctx ts t ppf =
  match ts with

  | [] ->
     print ppf "%t" (ty ctx t)

  | (x,u) :: ts when not (Value.occurs_ty t) ->
      print ~at_level:3 ppf "%t ->@ %t"
        (ty ~max_level:2 ctx u)
        (prod ctx ts t)

  | ts ->
     print ppf "forall %t,@ %t"
           (sequence (binder ctx) ts)
           (ty ~max_level:3 ctx t)

(** [lambda ctx a e t ppf] prints a lambda abstraction using formatter [ppf]. *)
and lambda ctx a e t ppf =
  print ppf "fun %t =>%t@ %t"
        (sequence (binder ctx) a)
        (annot (ty ~max_level:4 ctx t))
        (term ~max_level:4 ctx e)

and term ?max_level ctx (e,_) ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
    match e with
      | Value.Type ->
        print ~at_level:0 "Type"

      | Value.Name x ->
        print ~at_level:0 "%t" (name x)

      | Value.Bound k ->
        print ~at_level:0 "DEBRUIJN[%d]" k

      | Value.Lambda (a, (e, t)) ->
        print ~at_level:3 "%t" (lambda ctx a e t)

      | Value.Spine (e, (es, _)) ->
        (* XXX: no typing annotations yet *)
        print ~at_level:1 "@[<hov 2>%t@ %t@]"
          (term ~max_level:1 ctx e)
          (sequence (term ~max_level:0 ctx) (List.map (fun (_,(e,_)) -> e) es))

      | Value.Prod (ts, t) ->
        print ~at_level:3 "%t" (prod ctx ts t)

      | Value.Eq (t, e1, e2) ->
        print ~at_level:2 "@[<hv 2>%t@ ==%t %t@]"
          (term ~max_level:1 ctx e1)
          (annot (ty ~max_level:4 ctx t))
          (term ~max_level:1 ctx e2)

      | Value.Refl (t, e) ->
        print ~at_level:0 "refl%t %t"
          (annot (ty ~max_level:4 ctx t))
          (term ~max_level:0 ctx e)

and ty ?max_level ctx (Value.Ty t) ppf = term ?max_level ctx t ppf

let value ?max_level ctx v ppf =
  let (e,t) = v in
    print ~at_level:0 ppf "%t : %t"
          (term ~max_level:0 ctx e)
          (ty ~max_level:0 ctx t)

let context ctx ppf =
  print ppf "---------@." ;
  List.iter
    (fun (x, t) ->
     print ppf "@[<hov 4>Parameter %t@;<1 -2>: %t@]@\n" (name x) (ty ctx t))
    (List.rev (Context.free_list ctx)) ;
  print ppf "---END---@."
