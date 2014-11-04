(** Pretty-printing of Andromedan type theory. *)

(** Printing of messages. *)

let verbosity = ref 4
let annotate = ref false

module StringSet = Set.Make(struct
                                type t = string
                                let compare = compare
                            end)

let displayable = ref (StringSet.singleton "all")

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
  if StringSet.mem category (!displayable) then
    message "Debug" 3 msg
  else
    message "Dummy" (!verbosity + 1) msg

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

let name x ppf = print ~at_level:0 ppf "%s" x

(** [prod ctx x t1 t2 ppf] prints a dependent product using formatter [ppf]. *)
let rec prod ?max_level ctx x t1 t2 ppf =
  let x, ctx' = Context.add_fresh x t1 ctx in
  let t2' = Syntax.instantiate_ty (Syntax.mk_name ~loc:Position.Nowhere x) t2 in
    if Syntax.occurs_ty t2
    then
      print ?max_level ~at_level:3 ppf "forall (%s :@ %t), @ %t"
        x
        (ty ~max_level:4 ctx t1)
        (ty ~max_level:3 ctx' t2')
    else
      print ?max_level ~at_level:3 ppf "%t ->@ %t"
        (ty ~max_level:4 ctx t1)
        (ty ~max_level:3 ctx' t2')

(** [lambda ctx x t u e ppf] prints a lambda abstraction using formatter [ppf]. *)
and lambda ctx x t u e ppf =
  let x, ctx' = Context.add_fresh x t ctx in
  let x' = Syntax.mk_name ~loc:Position.Nowhere x in
  let u = Syntax.instantiate_ty x' u in
  let e = Syntax.instantiate x' e in
    print ~max_level:4 ppf "fun (%s :@ %t) =>%t@ %t"
      x
      (ty ~max_level:4 ctx t)
      (annot (ty ~max_level:4 ctx' u))
      (term ~max_level:4 ctx' e)

and term ?max_level ctx (e,_) ppf =
  let print' = print
  and print ?at_level = print ?max_level ?at_level ppf in
    match e with

      | Syntax.Name x ->
        print ~at_level:0 "%s" x

      | Syntax.Bound k ->
        print ~at_level:0 "DEBRUIJN[%d]" k

      | Syntax.Ascribe (e, t) ->
        print ~at_level:4 "%t :: %t"
          (term ~max_level:3 ctx e)
          (ty ~max_level:4 ctx t)

      | Syntax.Lambda (x, t, u, e) ->
        print ~at_level:3 "%t" (lambda ctx x t u e)

      | Syntax.App ((x, t, u), e1, e2) ->
          print ~at_level:1 "@[<hov 2>%t%t@ %t@]"
          (term ~max_level:1 ctx e1)
          (annot ~prefix:" @"
             (fun ppf -> 
               let x, ctx' = Context.add_fresh x t ctx in
               let u = Syntax.instantiate_ty (Syntax.mk_name ~loc:Position.Nowhere x) u in
                 print' ~max_level:4 ppf "%s :@ %t .@ %t"
                   x
                   (ty ~max_level:4 ctx t)
                   (ty ~max_level:4 ctx' u)))
          (term ~max_level:0 ctx e2)

      | Syntax.Type ->
        print ~at_level:0 "Type"

      | Syntax.Refl (t, e) ->
        print ~at_level:0 "refl%t %t"
          (annot (ty ~max_level:4 ctx t))
          (term ~max_level:0 ctx e)

      | Syntax.Prod (x, t1, t2) ->
        print ~at_level:3 "%t" (prod ctx x t1 t2)

      | Syntax.Eq (t, e1, e2) ->
        print ~at_level:2 "@[<hv 2>%t@ ==%t %t@]"
          (term ~max_level:1 ctx e1)
          (annot (ty ~max_level:4 ctx t))
          (term ~max_level:1 ctx e2)

and ty ?max_level ctx e ppf = term ?max_level ctx e ppf

let value ?max_level ctx v ppf =
  match v with
    | Syntax.Judge (e, t) ->
      print ~at_level:0 ppf "%t : %t"
        (term ~max_level:0 ctx e)
        (ty ~max_level:0 ctx t)

    | Syntax.String s ->
      print ~at_level:0 ppf "\"%s\"" (String.escaped s)

let context ctx ppf =
  print ppf "---------@." ;
  List.iter (fun (x, entry) ->
    match entry with
      | Context.Entry_free t ->
        print ppf "@[<hov 4>Parameter %s@;<1 -2>: %t@]@\n" x (ty ctx t)
      | Context.Entry_value v ->
        print ppf "@[<hov 4>Let %s@;<1 -2>:= %t@]@\n" x (value ctx v)
  ) ctx ;
  print ppf "---END---@."
