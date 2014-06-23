(** Pretty-printing of Brazilian type theory. *)

(** Printing of messages. *)

let verbosity = ref 2
let annotate = ref false

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
let debug msg = message "Debug" 3 msg

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

let universe u ppf =
  print ~at_level:0 ppf "%s" (Universe.to_string u)

let label lbl x ppf =
  if lbl = x then
    print ~at_level:0 ppf "%s" lbl
  else
    print ~at_level:0 ppf "%s as %s" lbl x

(** [prod xs x t1 t2 ppf] prints a dependent product using formatter [ppf]. *)
let rec prod ?max_level xs x t1 t2 ppf =
  if Syntax.occurs_ty 0 t2 then
    let x = find_name x xs in
      print ?max_level ~at_level:3 ppf "forall (%s :@ %t), @ %t"
        x
        (ty ~max_level:4 xs t1)
        (ty ~max_level:3 (x :: xs) t2)
  else
    print ?max_level ~at_level:3 ppf "%t ->@ %t"
      (ty ~max_level:4 xs t1)
      (ty ~max_level:3 (Input.anonymous :: xs) t2)

(** [name_prod xs x e1 e2 ppf] prints a dependent product name using formatter [ppf]. *)
and name_prod ?max_level xs x e1 e2 ppf =
  if Syntax.occurs 0 e2 then
    let x = find_name x xs in
      print ?max_level ~at_level:3 ppf "forall (%s :@ %t), @ %t"
        x
        (term ~max_level:4 xs e1)
        (term ~max_level:3 (x :: xs) e2)
  else
    print ?max_level ~at_level:3 ppf "%t ->@ %t"
      (term ~max_level:2 xs e1)
      (term ~max_level:3 (Input.anonymous :: xs) e2)

and record_fields xs lst ppf =
  let rec fold xs = function
    | [] -> ()
    | [(lbl,(x,t,e))] ->
      print ~at_level:0 ppf "%t@ =%t@ %t"
        (label lbl x) (annot (ty ~max_level:4 xs t)) (term ~max_level:4 xs e)
    | (lbl,(x,t,e)) :: lst ->
      print ~at_level:0 ppf "%t@ =%t@ %t;@ "
        (label lbl x) (annot (ty ~max_level:4 xs t)) (term ~max_level:4 xs e) ;
      fold (x::xs) lst
  in
    fold xs lst

and name_record_ty_fields xs lst ppf =
  let rec fold xs = function
    | [] -> ()
    | [(lbl,(x,u,e))] ->
      print ~at_level:0 ppf "%t:%t@ %t"
        (label lbl x) (annot (universe u)) (term ~max_level:4 xs e)
    | (lbl,(x,u,e)) :: lst ->
      print ~at_level:0 ppf "%t:%t@ %t;@ "
        (label lbl x) (annot (universe u)) (term ~max_level:4 xs e) ;
      fold (x::xs) lst
  in
    fold xs lst

and record_ty_fields xs lst ppf =
  let rec fold xs = function
    | [] -> ()
    | [(lbl,(x,t))] ->
      print ~at_level:0 ppf "%t:@ %t"
        (label lbl x) (ty ~max_level:4 xs t)
    | (lbl,(x,t)) :: lst ->
      print ~at_level:0 ppf "%t:@ %t;@ "
        (label lbl x) (ty ~max_level:4 xs t) ;
      fold (x::xs) lst
  in
    fold xs lst

(** [lambda xs x t u e ppf] prints a lambda abstraction using formatter [ppf]. *)
and lambda xs x t u e ppf =
  let rec collect xs y ys t e =
    let y =
      if Syntax.occurs_ty 0 u || Syntax.occurs 0 e
      then find_name y xs
      else Input.anonymous
    in
      match fst e with
        | Syntax.Lambda (z, t', u, e') ->
          if Syntax.equal_ty (Syntax.shift_ty 1 t) t'
          then collect (y::xs) z (y::ys) t' e'
          else (y::xs, y::ys, e)
        | _ ->
          (y::xs, y::ys, e)
  in
  let rec abstraction xs x t u e ppf =
    if !annotate then
      print ~max_level:4 ppf "(%s :@ %t) =>%t@ %t"
        x
        (ty ~max_level:4 xs t)
        (ty ~max_level:4 (x::xs) u)
        (term ~max_level:4 (x::xs) e)
    else
      let (xs', ys, e) = collect xs x [] t e in
      let ys = List.rev ys in
        print ~at_level:0 ppf "(%t :@ %t)@ "
          (sequence name ys)
          (ty ~max_level:4 xs t) ;
        match fst e with
          | Syntax.Lambda (x, t, u, e) -> abstraction xs' x t u e ppf
          | _ -> print ~at_level:0 ppf "=>@ %t" (term ~max_level:4 xs' e)
  in
    print ~at_level:3 ppf "@[<hov>fun %t@]" (abstraction xs x t u e)

and term ?max_level xs (e,_) ppf =
  let print' = print
  and print ?at_level = print ?max_level ?at_level ppf in
    match e with

      | Syntax.Var k ->
          begin
            try
              (*if (!annotate) then                           *)
              (*  print ~at_level:0 "%s<%d>" (List.nth xs k) k*)
              (*else                                          *)
                print ~at_level:0 "%s" (List.nth xs k)
            with
              _ ->
                print ~at_level:0 "BAD_INDEX[%d/%d]" k (List.length xs)
          end

      | Syntax.Equation (e1, t, e2) ->
        print ~at_level:4 "equation %t%t@ in %t"
          (term ~max_level:3 xs e1)
          (annot (ty ~max_level:4 xs t))
          (term ~max_level:4 xs e2)

      | Syntax.Rewrite (e1, t, e2) ->
        print ~at_level:4 "rewrite %t%t@ in %t"
          (term ~max_level:3 xs e1)
          (annot (ty ~max_level:4 xs t))
          (term ~max_level:4 xs e2)

      | Syntax.Ascribe (e, t) ->
        print ~at_level:4 "%t :: %t"
          (term ~max_level:3 xs e)
          (ty ~max_level:4 xs t)

      | Syntax.Lambda (x, t, u, e) ->
        print ~at_level:3 "%t" (lambda xs x t u e)

      | Syntax.App ((x, t, u), e1, e2) ->
        print ~at_level:1 "%t@,%t@ %t"
          (term ~max_level:1 xs e1)
          (annot ~prefix:" @"
             (fun ppf -> print' ~max_level:4 ppf "%s :@ %t .@ %t"
                           x
                           (ty ~max_level:4 xs t)
                           (ty ~max_level:4 (x::xs)
                           u)))
          (term ~max_level:0 xs e2)

      | Syntax.Record lst ->
        print ~at_level:0 "{%t}" (record_fields xs lst)

      | Syntax.Project (e, _, lbl) ->
        print ~at_level:0 "%t.%s" (term ~max_level:0 xs e) lbl

      | Syntax.UnitTerm -> print ~at_level:0 "()"

      | Syntax.Idpath (t, e) -> print ~at_level:0 "idpath%t %t"
        (annot (ty ~max_level:4 xs t))
        (term ~max_level:0 xs e)

      | Syntax.J (t, (x, y, p, u), (z, e1), e2, e3, e4) ->
        print ~at_level:1 "J (%t, [%s %s %s . %t], [%s . %t], %t, %t, %t)"
          (ty ~max_level:4 xs t)
          x y p (ty ~max_level:4 (p::y::x::xs) u)
          z (term ~max_level:4 (z::xs) e1)
          (term ~max_level:4 xs e2)
          (term ~max_level:4 xs e3)
          (term ~max_level:4 xs e4)

      | Syntax.Refl (t, e) ->
        print ~at_level:0 "refl%t %t"
          (annot (ty ~max_level:4 xs t))
          (term ~max_level:0 xs e)

      | Syntax.Coerce (u1, u2, e) ->
        print ~at_level:1 "coerce (%t,@ %t,@ %t)"
          (universe u1)
          (universe u2)
          (term ~max_level:4 xs e)

      | Syntax.NameRecordTy lst ->
        print ~at_level:0 "{%t}" (name_record_ty_fields xs lst)

      | Syntax.NameUnit -> print ~at_level:0 "unit"

      | Syntax.NameProd (_, _, x, e1, e2) ->
        print ~at_level:3 "%t" (name_prod xs x e1 e2)

      | Syntax.NameUniverse u ->
        print ~at_level:1 "Universe %t"
          (universe u)

      | Syntax.NamePaths (_, e1, e2, e3) ->
        print ~at_level:2 "@[<hv 2>%t@ =%t@ %t@]"
          (term ~max_level:1 xs e2)
          (annot (term ~max_level:4 xs e1))
          (term ~max_level:1 xs e3)

      | Syntax.NameId (_, e1, e2, e3) ->
        print ~at_level:2 "@[<hv 2>%t@ ==%t@ %t@]"
          (term ~max_level:1 xs e2)
          (annot (term ~max_level:4 xs e1))
          (term ~max_level:1 xs e3)

and ty ?max_level xs (t,_) ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
    match t with

      | Syntax.Universe u ->
        print ~at_level:1 "Universe %t"
          (universe u)

      | Syntax.El (u, e) ->
          if (!annotate) then
            print "El(%t, %t)" (universe u) (term ~max_level:4 xs e)
          else
            print "%t"
              (term ?max_level xs e)

      | Syntax.RecordTy lst ->
        print ~at_level:0 "{%t}" (record_ty_fields xs lst)

      | Syntax.Unit ->
        print ~at_level:0 "unit"

      | Syntax.Prod (x, t1, t2) ->
        print ~at_level:3 "%t" (prod xs x t1 t2)

      | Syntax.Paths (t, e1, e2) ->
        print ~at_level:2 "@[<hv 2>%t@ =%t %t@]"
          (term ~max_level:1 xs e1)
          (annot (ty ~max_level:4 xs t))
          (term ~max_level:1 xs e2)

      | Syntax.Id (t, e1, e2) ->
        print ~at_level:2 "@[<hv 2>%t@ ==%t %t@]"
          (term ~max_level:1 xs e1)
          (annot (ty ~max_level:4 xs t))
          (term ~max_level:1 xs e2)

