(** Variable names *)

type fixity =
  | Word
  | Anonymous of int
  | Prefix
  | Infix of Level.infix

type ident = Ident of string * fixity

type atom = Atom of string * fixity * int

type meta = Meta of string * fixity * int

type constant = ident
type constructor = ident

type operation = ident
type ty = ident
type aml_constructor = ident

(** Make a nice subscript from an integer. *)
let subscript k =
  let subdigit = [|"₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"|] in
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

(** Convert an integer to a Greek letter, possibly subscripted. *)
let greek k =
  let greek = [| ("α", "a"); ("β", "b"); ("γ", "c"); ("δ", "d"); ("ε", "e") |] in
  let n = Array.length greek in
  let i = k / n in
  let j = k mod n in
  let base = (if !Config.ascii then snd greek.(j) else fst greek.(j)) in
  if i = 0 then base else (base ^ subscript i)

let print_ident ?(parentheses=true) x ppf =
  match x with
  | Ident (s, Word) -> Format.fprintf ppf "%s" s
  | Ident (_, Anonymous k) -> Format.fprintf ppf "_"
  | Ident (s, (Prefix|Infix _)) ->
     if parentheses then
       Format.fprintf ppf "( %s )" s
     else
       Format.fprintf ppf "%s" s

let print_op = print_ident ~parentheses:true

let anonymous =
  let k = ref (-1) in
  fun () ->
  incr k ;
  Ident ("anon", Anonymous !k)

let is_anonymous = function
  | Ident (_, Anonymous _) -> true
  | _ -> false

let make ?(fixity=Word) s = Ident (s, fixity)

module Predefined = struct

  (** Booleans *)

  let bool = make "mlbool"

  let mlfalse = make "mlfalse"

  let mltrue = make "mltrue"

  (** Lists *)

  let list = make "list"

  let nil = make "[]"

  let cons = make ~fixity:(Infix Level.InfixCons) "::"

  (** Comparison *)

  let mlorder = make "mlorder"

  let mlless = make "mlless"

  let mlequal = make "mlequal"

  let mlgreater = make "mlgreater"

  (** Option type *)

  let option = make "option"

  let some = make "Some"

  let none = make "None"

  (** Builtin commands *)

  let equal_term = make "equal_term"

  let equal_type = make "equal_type"

  let coercible_ty = make "coercible"

  let coercible_constructor = make "Coercible"

  let convertible = make "Convertible"

  let notcoercible = make "NotCoercible"

  let coerce = make "coerce"

  let hypotheses = make "hypotheses"
end

let fresh =
  let counter = ref (-1) in
  function Ident (s, fixity) ->
    incr counter;
    Atom (s, fixity, !counter)

let ident_of_atom (Atom (s,fixity,_)) = Ident (s,fixity)

(** Split a string into base and an optional numerical suffix, e.g., ["x42"],
   ["x₄₂"], and ["x4₂"] are split into [("x", Some 42)], while ["xy"] is split into [("xy",
   None)]. *)
let extract_suffix s =
  let digits =
    [("0",0); ("1",1); ("2",2); ("3",3); ("4",4); ("5",5); ("6",6); ("7",7); ("8",8); ("9",9);
     ("₀",0); ("₁",1); ("₂",2); ("₃",3); ("₄",4); ("₅",5); ("₆",6); ("₇",7); ("₈",8); ("₉",9)]
  in
  let rec ends_with i = function
    | [] -> None
    | (c, d) :: lst ->
       let k = String.length c in
       let c' = if i + 1 - k >= 0 then String.sub s (i + 1 - k) k else "FOO" in
       if i + 1 - k >= 0 && c = c'
       then Some (d, i - k)
       else ends_with i lst
  in

  (* Convert a list of digits in reverse order to an integer *)
  let rec as_int k = function
    | [] -> k
    | d :: ds -> as_int (10 * k + d) ds
  in

  let n = String.length s in
  let rec extract suffix i =
    if i < 0 then
      (* If we get here [s] is made of digits only. *)
      (s, None)
    else
      match ends_with i digits with
      | None ->
         if i = n - 1
         then (s, None)
         else (String.sub s 0 (i+1), Some (as_int 0 suffix))
      | Some (d, i) ->
         extract (d :: suffix) i
  in
  extract [] (n-1)

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
    while used (s ^ subscript !k) xs do incr k done;
    Ident (s ^ subscript !k, fixity)

let eq_ident (x : ident) (y : ident) = (x = y)

(* XXX why do we compare fixities? *)
let compare_ident (x : ident) (y : ident) = Pervasives.compare x y

module IdentSet = Set.Make (struct
                    type t = ident
                    let compare = compare_ident
                  end)

module IdentMap = Map.Make (struct
                    type t = ident
                    let compare = compare_ident
                  end)

let eq_atom (Atom (_, _, k)) (Atom (_, _, m)) = (k = m)

let compare_atom (Atom (_, _, x)) (Atom (_, _, y)) =
  if x < y then -1 else if x > y then 1 else 0

module AtomSet = Set.Make (struct
                    type t = atom
                    let compare = compare_atom
                  end)

module AtomMap = Map.Make (struct
                    type t = atom
                    let compare = compare_atom
                  end)

let fresh_meta =
  let counter = ref (-1) in
  function Ident (s, fixity) ->
    incr counter;
    Meta (s, fixity, !counter)

let ident_of_meta (Meta (s, fixity, _)) = Ident (s, fixity)

let eq_meta (Meta (_, _, k)) (Meta (_, _, m)) = (k = m)

let compare_meta (Meta (_, _, x)) (Meta (_, _, y)) =
  if x < y then -1 else if x > y then 1 else 0

module MetaSet = Set.Make (struct
                    type t = meta
                    let compare = compare_meta
                  end)

module MetaMap = Map.Make (struct
                    type t = meta
                    let compare = compare_meta
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

let level_of_ident x ys = index_of_ident x (List.rev ys)

let rec assoc_ident x = function
  | [] -> None
  | (y,v)::_ when (eq_ident x y) -> Some v
  | _::l -> assoc_ident x l

let print_debruijn xs k ppf =
  let x = List.nth xs k in
  print_ident x ppf

(* We expect that most atoms are never printed. Therefore,
   for the purposes of printing, we remap the ones that do get printed
   so that the user sees them numbered consecutively starting from 0. *)
let reindex_atom = ref AtomMap.empty
let next_atom = ref 0

let print_atom_subs ?(parentheses=true) x ppf =
  match x with
  | Atom (s, Word, k) ->
     Format.fprintf ppf "%s%s" s (subscript k)

  | Atom (_, Anonymous j, k) ->
     Format.fprintf ppf "anon%d%s" j (subscript k)

  | Atom (s, (Prefix|Infix _), k) ->
     if parentheses then
       Format.fprintf ppf "( %s%s )" s (subscript k)
     else
       Format.fprintf ppf "%s%s" s (subscript k)

let print_atom ?parentheses x ppf =
  let y =
    try
      AtomMap.find x !reindex_atom
    with
      Not_found ->
        let n = !next_atom in
        let y = match x with Atom (s,fixity,_) -> Atom (s,fixity,n) in
        reindex_atom := AtomMap.add x y !reindex_atom ;
        next_atom := n + 1;
        y
  in
  print_atom_subs ?parentheses y ppf

(* We expect that most meta-variables are never printed. Therefore,
   for the purposes of printing, we remap the ones that do get printed
   so that the user sees them numbered consecutively starting from 0. *)
let reindex_meta = ref MetaMap.empty
let next_meta = ref 0

let print_meta_subs ?(parentheses=true) x ppf =
  match x with
  | Meta (s, Word, k) ->
     Format.fprintf ppf "%s%s" s (subscript k)

  | Meta (_, Anonymous j, k) ->
     Format.fprintf ppf "anon%d%s" j (subscript k)

  | Meta (s, (Prefix|Infix _), k) ->
     if parentheses then
       Format.fprintf ppf "( %s%s )" s (subscript k)
     else
       Format.fprintf ppf "%s%s" s (subscript k)

let print_meta ?parentheses x ppf =
  let y =
    try
      MetaMap.find x !reindex_meta
    with
      Not_found ->
        let n = !next_meta in
        let y = match x with Meta (s,fixity,_) -> Meta (s,fixity,n) in
        reindex_meta := MetaMap.add x y !reindex_meta;
        next_meta := n + 1;
        y
  in
  print_meta_subs ?parentheses y ppf

module Json =
struct
  let ident = function
    | Ident (s, Anonymous k) -> Json.tuple [Json.String s; Json.Int k]
    | Ident (s, (Word|Prefix|Infix _)) -> Json.String s

  let atom (Atom (s, _, k)) = Json.tuple [Json.String s; Json.Int k]

  let meta (Meta (s, _, k)) = Json.tuple [Json.String s; Json.Int k]

  let atomset s = Json.List (List.map atom (AtomSet.elements s))

  let atommap s = Json.List (List.map (fun (x, _) -> atom x) (AtomMap.bindings s))

  let metamap s = Json.List (List.map (fun (x, _) -> meta x) (MetaMap.bindings s))

end
