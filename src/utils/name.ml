(** Variable names *)

type fixity =
  | Word
  | Anonymous
  | Prefix
  | Infix0
  | Infix1
  | Infix2
  | Infix3
  | Infix4

type ident = Ident of string * fixity

type atom = Atom of string * fixity * int

type label = ident

let print_ident x ppf =
  match x with
  | Ident (s, Word) -> Print.print ppf "%s" s
  | Ident (_, Anonymous) -> Print.print ppf "_"
  | Ident (s, (Prefix|Infix0|Infix1|Infix2|Infix3|Infix4)) -> Print.print ppf "( %s )" s

let print_label = print_ident

(** Subscripts *)

let subdigit = [|"₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"|]

let subscript k =
  if !Config.ascii then "_" ^ string_of_int k
  else if k = 0 then subdigit.(0)
  else
    let rec fold s = function
      | 0 -> s
      | k ->
         let s = subdigit.(k mod 10) ^ s in
         fold s (k / 10)
    in
    fold "" k

let print_atom x ppf =
  match x with
  | Atom (s, Word, k) -> Print.print ppf "%s%s" s (subscript k)
  | Atom (_, Anonymous, k) -> Print.print ppf "_%s" (subscript k)
  | Atom (s, (Prefix|Infix0|Infix1|Infix2|Infix3|Infix4), k) -> Print.print ppf "( %s%s )" s (subscript k)

let print_op = print_ident

let anonymous = Ident ("_", Anonymous)

let make ?(fixity=Word) s = Ident (s, fixity)

let fresh =
  let counter = ref (-1) in
  function Ident (s, fixity) ->
    incr counter;
    if !counter < 0 then
      Error.impossible ~loc:Location.unknown "More than %d fresh names generated." max_int
    else
      Atom (s, fixity, !counter)

(** Split a string into base and an optional numerical suffix, e.g.,
    ["x42"] is split into [("x", Some 42)], while ["xy"] is split into
    [("xy", None)]. *)
let extract_suffix s =
  let n = String.length s in
  let i = ref (n - 1) in
  while !i >= 0 && '0' <= s.[!i] && s.[!i] <= '9' do decr i done;
  if !i < 0 || !i = n - 1 then
    (s, None)
  else
    let base = String.sub s 0 (!i + 1)
    and suffix = String.sub s (!i + 1) (n - !i - 1) in
    (base, Some (int_of_string suffix))

let refresh xs ((Ident (s, fixity)) as x) =
  let rec used s = function
      | [] -> false
      | Ident (t, _) :: lst -> s = t || used s lst
  in
  if not (used s xs) then
     x
  else
    let (s, k) = extract_suffix s in
    let k = ref (match k with Some k -> k | None -> 0) in
    while used (s ^ string_of_int !k) xs do incr k done;
    Ident (s ^ string_of_int !k, fixity)

let eq_ident (Ident (x, _)) (Ident (y, _)) = (x = y)

let compare_ident (Ident (x, _)) (Ident (y, _)) = compare x y

module IdentMap = Map.Make (struct
                    type t = ident
                    let compare = compare_ident
                  end)

let eq_label = eq_ident

let eq_atom (Atom (_, _, k)) (Atom (_, _, m)) = (k = m)

let compare_atom (Atom (_, _, x)) (Atom (_, _, y)) =
  if x < y then -1 else if x > y then 1 else 0

module AtomSet = Set.Make (struct
                    type t = atom
                    let compare = compare_atom
                  end)

let index_of_atom x ys =
  let rec fold k = function
    | [] -> None
    | y :: ys -> if eq_atom x y then Some k else fold (k + 1) ys
  in
  fold 0 ys

let index_of_ident x ys =
  let rec fold k = function
    | [] -> None
    | y :: ys -> if eq_ident x y then Some k else fold (k + 1) ys
  in
  fold 0 ys

let print_binder1 print_u xs x u ppf =
  Print.print ppf "(@[<hv>%t :@ %t@])"
    (print_ident x) (print_u xs u)

let rec print_binders print_xu print_v xs xus ppf =
  match xus with
  | [] -> Print.print ppf "%t" (print_v xs)
  | [(x,u)] ->
    let x = refresh xs x in
    Print.print ppf "%t,@,%t"
      (print_xu xs x u)
      (print_v (x::xs))
  | (x,u) :: xus ->
    let x = refresh xs x in
    Print.print ppf "%t@ %t"
      (print_xu xs x u)
      (print_binders print_xu print_v (x::xs) xus)
