(** Pretty-printing of termessions with the Ocaml [Format] library. *)

module S = Syntax

(** Support for printing of errors, warning and debugging information. *)

let default_verbosity = 2
let verbosity = ref default_verbosity

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


(** Given a variable [x] and a list of variable names [xs], find a variant of [x] which
    does not appear in [xs]. *)
let find_name x xs =
  (** Split a variable name into base and numerical postfix, e.g.,
      ["x42"] is split into [("x", 42)]. *)
  let split s =
    let n = String.length s in
    let i = ref (n - 1) in
      while !i >= 0 && '0' <= s.[!i] && s.[!i] <= '9' do decr i done ;
      if !i < 0 || !i = n - 1
      then (s, None)
      else
        let k = int_of_string (String.sub s (!i+1) (n - !i - 1)) in
          (String.sub s 0 (!i+1), Some k)
  in

  if not (List.mem x xs)
  then x
  else
    let (y, k) = split x in
    let k = ref (match k with Some k -> k | None -> 0) in
      while List.mem (y ^ string_of_int !k) xs do incr k done ;
      y ^ string_of_int !k

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
    let x = find_name x xs in
      print ~at_level:3 ppf "(%s :@ %t) ->@ %t"
             x (term ~max_level:2 xs t1) (term (x :: xs) t2)
  else
    print ~at_level:3 ppf "%t ->@ %t" (term ~max_level:2 xs t1) (term ("_" :: xs) t2)

(** [tpi xs a ppf] prints abstraction [a] as dependent product using formatter [ppf]. *)
and sigma ?max_level xs x t1 t2 ppf =
  if S.occurs 0 t2 then
    let x = find_name x xs in
      print ~at_level:3 ppf "(%s :@ %t) *@ %t"
             x (term ~max_level:2 xs t1) (term (x :: xs) t2)
  else
    print ~at_level:3 ppf "%t *@ %t"
      (term ~max_level:2 xs t1) (term ~max_level:2 ("_" :: xs) t2)

(** [lambda xs x t e ppf] prints function [fun x => e] using formatter [ppf]. *)
and lambda xs x t e ppf =
  let x =
    if S.occurs 0 e
    then find_name x xs
    else "_"
  in
    print ~at_level:3 ppf "fun %s : %t =>@ %t" x (term ~max_level:2 xs t) (term (x :: xs) e)

(** [term ctx e ppf] prints term [e] using formatter [ppf]. *)
  and term ?max_level xs e ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
      if not (Format.over_max_boxes ()) then
        match e with
          | S.Var k -> print "%s" (List.nth xs k)
          | S.Lambda (x, t, _, e) -> print ~at_level:3 "%t" (lambda xs x t e)
          | S.App (e1, e2) -> print ~at_level:1 "%t@ %t" (term ~max_level:1 xs e1) (term ~max_level:0 xs e2)
          | S.Pair (e1, e2, _, _, _) -> print ~at_level:0 "(%t,@ %t)" (term ~max_level:1 xs e1) (term ~max_level:0 xs e2)
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
              print "@[<hov>(%t@ %s@ %t @@ %t)@]"
              (term ~max_level:1 xs e1)
              (match o with S.Pr -> "=" | S.Ju -> "==")
              (term ~max_level:1 xs e2)
              (term ~max_level:1 xs t)
          | S.Ind_eq(o, t, (x,y,p,c), (z,w), a, b, q) ->
              print "%s(%t, %s.%s.%s.%t, %s.%t, %t, %t, %t)"
              (match o with S.Pr -> "J_F" | S.Ju -> "J")
              (term ~max_level:3 xs t)
              x y p
              (term ~max_level:3 (p::y::x::xs) c)
              z
              (term ~max_level:3 (z::xs) w)
              (term ~max_level:3 xs a)
              (term ~max_level:3 xs b)
              (term ~max_level:3 xs q)
          | S.U (S.NonFib i) -> print "QuasiType %d" i
          | S.U (S.Fib i)  -> print "Type %d" i
          | S.Base (S.TUnit) -> print "unit"
          | S.Const (S.Unit) -> print "()"
          | S.Handle (e, es) ->
              print ~at_level:3 "handle %t with %t"
              (term xs e)
              (sequence ~sep:" | " (term xs) es)
          | S.MetavarApp mva ->
              begin
                match S.get_mva mva with
                | Some defn -> print ~at_level:0 "%t" (term ~max_level:1 xs defn)
                | None ->
                    if (!verbosity > default_verbosity) then
                      print "%s" (S.string_of_mva mva)
                    else
                      print "?"
              end

