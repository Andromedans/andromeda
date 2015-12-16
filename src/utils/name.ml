(** Variable names *)

type ident =
  | Anonymous
  | String of string

type atom =
  | Gensym of string * int

type label = ident

let print_ident x ppf =
  match x with
  | Anonymous -> Print.print ppf "_"
  | String s -> Print.print ppf "%s" s

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
  match x with Gensym (s, k) -> Print.print ppf "%s%s" s (subscript k)

let print_op op ppf =
  Print.print ppf "#%s" op

let anonymous = Anonymous

let make s = String s

let fresh =
  let counter = ref (-1) in
  fun x ->
    incr counter;
    if !counter < 0 then
      Error.impossible ~loc:Location.unknown "More than %d fresh names generated." max_int;
    let s =
      match x with
      | Anonymous -> "_"
      | String s -> s
    in
    Gensym (s, !counter)

let refresh_atom (Gensym (a, _)) = fresh (String a)

let fresh_candy =
  let counter = ref (-1) in
  fun () ->
    incr counter;
    if !counter < 0 then
      Error.impossible ~loc:Location.unknown "More than %d names of sugar generated." max_int;
    String ("sugar var " ^ (string_of_int !counter))

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

(** [find_name s xs] finds a name derived from a string [s] that does not yet
    appear in [xs]. *)
let find_name s xs =
  if not (List.mem (String s) xs) then
    String s
  else
    let (s, k) = extract_suffix s in
    let k = ref (match k with Some k -> k | None -> 0) in
    while List.mem (String (s ^ string_of_int !k)) xs do incr k done;
    String (s ^ string_of_int !k)

let refresh xs = function
  | Anonymous -> Anonymous
  | String s -> find_name s xs

let eq_ident x y = (x = y)

let eq_label = eq_ident

let eq_atom (Gensym (_, x)) (Gensym (_, y)) = (x = y)

let compare_atom (Gensym (_, x)) (Gensym (_, y)) =
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
  Print.print ppf "[@[<hv>%t :@ %t@]]"
    (print_ident x) (print_u xs u)

let rec print_binders print_xu print_v xs xus ppf =
  match xus with
  | [] -> Print.print ppf "%t" (print_v xs)
  | [(x,u)] ->
    let x = refresh xs x in
    Print.print ppf "%t@,%t"
      (print_xu xs x u)
      (print_v (x::xs))
  | (x,u) :: xus ->
    let x = refresh xs x in
    Print.print ppf "%t@ %t"
      (print_xu xs x u)
      (print_binders print_xu print_v (x::xs) xus)
