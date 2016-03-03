(** Variable names *)

type fixity =
  | Word
  | Anonymous
  | Prefix
  | Infix of Level.infix

type ident = Ident of string * fixity

type atom = Atom of string * fixity * int

type label = ident
type signature = ident
type constant = ident
type data = ident
type operation = ident

let print_ident ?(parentheses=true) x ppf =
  match x with
  | Ident (s, Word) -> Format.fprintf ppf "%s" s
  | Ident (_, Anonymous) -> Format.fprintf ppf "_"
  | Ident (s, (Prefix|Infix _)) ->
     if parentheses then
       Format.fprintf ppf "( %s )" s
     else
       Format.fprintf ppf "%s" s

let print_label = print_ident ~parentheses:true

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

let print_atom ?(parentheses=true) x ppf =
  match x with
  | Atom (s, Word, k) ->
     Format.fprintf ppf "%s%s" s (subscript k)

  | Atom (_, Anonymous, k) ->
     Format.fprintf ppf "_%s" (subscript k)

  | Atom (s, (Prefix|Infix _), k) ->
     if parentheses then
       Format.fprintf ppf "( %s%s )" s (subscript k)
     else
       Format.fprintf ppf "%s%s" s (subscript k)


let print_op = print_ident ~parentheses:true

let anonymous = Ident ("_", Anonymous)

let is_anonymous = function
  | Ident (_, Anonymous) -> true
  | _ -> false

let make ?(fixity=Word) s = Ident (s, fixity)

let fresh =
  let counter = ref (-1) in
  function Ident (s, fixity) ->
    incr counter;
    if !counter < 0 then
      Error.impossible ~loc:Location.unknown "More than %d fresh names generated." max_int
    else
      Atom (s, fixity, !counter)

let ident_of_atom (Atom (s,fixity,_)) = Ident (s,fixity)

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

let rec assoc_ident x = function
  | [] -> None
  | (y,v)::_ when (eq_ident x y) -> Some v
  | _::l -> assoc_ident x l

let print_debruijn xs k ppf =
  try
    let x = List.nth xs k in
    if !Config.debruijn
    then Format.fprintf ppf "%t[%d]" (print_ident x) k
    else print_ident x ppf
  with
  | Failure "nth" ->
      Format.fprintf ppf "DEBRUIJN[%d]" k

