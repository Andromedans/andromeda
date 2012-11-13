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

(** Print the given source code position. *)
let position loc ppf =
  match loc with
  | Common.Nowhere ->
      Format.fprintf ppf "unknown position"
  | Common.Position (begin_pos, end_pos) ->
      let begin_char = begin_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol in
      let end_char = end_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol in
      let begin_line = begin_pos.Lexing.pos_lnum in
      let filename = begin_pos.Lexing.pos_fname in

      if String.length filename != 0 then
        Format.fprintf ppf "file %S, line %d, charaters %d-%d" filename begin_line begin_char end_char
      else
        Format.fprintf ppf "line %d, characters %d-%d" (begin_line - 1) begin_char end_char

(** Print the name of a variable. *)
let variable x ppf =
  match x with
    | Common.Anonymous -> print ppf "_"
    | Common.String x -> print ppf "%s" x
    | Common.Gensym (x, k) -> print ppf "%s_%d" x k

(** Print a sequence of things with the given (optional) separator. *)
let sequence ?(sep="") f lst ppf =
  let rec seq = function
    | [] -> print ppf ""
    | [x] -> print ppf "%t" (f x)
    | x :: xs -> print ppf "%t%s@ " (f x) sep ; seq xs
  in
    seq lst

(** [pi a ppf] prints abstraction [a] as dependent product using formatter [ppf]. *)
let rec pi a ppf =
  let rec collect (x, e1, e2) =
    match fst e2 with
      | (Syntax.Var _ | Syntax.Universe _ | Syntax.Lambda _ | Syntax.App _) -> [([x], e1)], e2
      | Syntax.Pi a ->
        begin match x, e1 with
          | Common.Anonymous, e1 -> let lst, e = collect a in ([x], e1) :: lst, e
          | _, _ ->
            (match collect a with
              | (ys, e1') :: lst, e when e1 = e1' -> (x::ys, e1') :: lst, e
              | lst, e -> ([x], e1) :: lst, e)
        end
  in
  let lst, e = collect a in
  let rec pi lst ppf =
    match lst with
      | [] -> print ppf ",@ %t" (expr e)
      | ([], _) :: _ -> assert false
      | [([Common.Anonymous], t)] -> print ppf "%t ->@ %t" (expr t) (expr e)
      | ([Common.Anonymous], t) :: lst -> print ppf "%t ->@ %t" (expr t) (pi lst)
      | (xs, t) :: lst -> print ppf "forall (%t :@ %t),@ %t" (sequence variable xs) (expr t) (pi lst)
  in
    print ppf "forall %t" (pi lst)

(** [lambda a ppf] prints abstraction [a] as a function using formatter [ppf]. *)
and lambda a ppf =
  let rec collect (x, e1, e2) =
    match fst e2 with
      | (Syntax.Var _ | Syntax.Universe _ | Syntax.Lambda _ | Syntax.App _) -> [([x], e1)], e2
      | Syntax.Pi a ->
        (match collect a with
          | (ys, e1') :: lst, e when e1 = e1' -> (x::ys, e1') :: lst, e
          | lst, e -> ([x], e1) :: lst, e)
  in
  let lst, e = collect a in
  let rec lambda lst ppf =
    match lst with
      | [] -> print ppf " =>@ %t" (expr e)
      | ([], _) :: lst -> assert false
      | (xs, t) :: lst -> print ppf "(%t :@ %t)@ %t" (sequence variable xs) (expr t) (lambda lst)
  in
    print ppf "fun %t" (lambda lst)

(** [expr e ppf] prints (beautified) expression [e] using formatter [ppf]. *)
and expr e ppf =
  let rec expr ?max_level (e, _) ppf =  expr'?max_level e ppf
  and expr' ?max_level e ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      match e with
        | Syntax.Var x -> variable x ppf
        | Syntax.Universe k -> print "Type %d" k
        | Syntax.Pi a -> pi a ppf
        | Syntax.Lambda a -> lambda a ppf
        | Syntax.App (e1, e2) -> print ~at_level:1 "%t@ %t" (expr ~max_level:1 e1) (expr ~max_level:0 e2)
  in
    expr (Beautify.beautify e) ppf
    
let expr' e ppf = expr (Common.nowhere e) ppf
  
(** Support for printing of errors, warning and debugging information. *)
let verbosity = ref 3
let message ?(loc=Common.Nowhere) msg_type v =
  if v <= !verbosity then
    begin
      Format.eprintf "%s at %t:@\n  @[" msg_type (position loc) ;
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let error (loc, err_type, msg) = message ~loc (err_type) 1 "%s" msg
let warning msg = message "Warning" 2 msg
let debug msg = message "Debug" 3 msg
