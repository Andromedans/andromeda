(** Variable names *)

type t =
  | Anonymous
  | Gensym of string * int
  | String of string

let print x ppf =
  match x with
  | Anonymous -> Print.print ppf "_"
  | Gensym (s, k) ->
    begin if !Config.verbosity <= 3
      then Print.print ppf "%s" s
      else Print.print ppf "gensym_%s_%d" s k
    end
  | String s -> Print.print ppf "%s" s

let print_op op ppf =
  Print.print ppf "#%s" op

let anonymous = Anonymous

let make s = String s

let fresh =
  let counter = ref (-1) in
  fun x ->
    incr counter;
    if !counter < 0 then
      Error.impossible "More than %d fresh names generated." max_int;
    let s =
      match x with
      | Anonymous -> "_"
      | String s -> s
      | Gensym (s, _) -> s
    in
    Gensym (s, !counter)

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
  | String s
  | Gensym (s, _) -> find_name s xs

let eq x y = (x = y)

let index_of x ys =
  let rec fold k = function
    | [] -> None
    | y :: ys -> if eq x y then Some k else fold (k + 1) ys
  in
  fold 0 ys

let print_binder1 print_u xs x u ppf =
  Print.print ppf "[@[<hv>%t :@ %t@]]"
    (print x) (print_u xs u)

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
