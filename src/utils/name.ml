(** Variable names *)

type fixity =
  | Word
  | Anonymous of int
  | Prefix
  | Infix of Level.infix

type t = { name : string ; fixity : fixity }

(** A name that is possibly qualified by a module *)
type path =
  | PName of t
  | PModule of path * t

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

let print ?(parentheses=true) {name;fixity} ppf =
  match fixity with
  | Word -> Format.fprintf ppf "%s" name
  | Anonymous _ -> Format.fprintf ppf "_"
  | (Prefix|Infix _) ->
     if parentheses then
       Format.fprintf ppf "( %s )" name
     else
       Format.fprintf ppf "%s" name

let rec print_path pth ppf =
  match pth with
  | PName x -> print x ppf
  | PModule (mdl, x) ->
     Format.fprintf ppf "%t.%t" (print_path mdl) (print x)

let anonymous =
  let k = ref (-1) in
  fun () ->
  incr k ;
  { name = "anon"; fixity = Anonymous !k }

let module_filename {name;_} = name ^ ".m31"

let mk_name ?(fixity=Word) name = {name; fixity}

module Builtin = struct

  (** The name of the module that contains the builtin entities. *)
  let ml_name = mk_name "ML"
  let ml = PName ml_name

  let in_ml x = PModule (ml, x)

  (** Booleans *)

  let bool_name = mk_name "bool"
  let bool = in_ml bool_name

  let mlfalse_name = mk_name "false"
  let mlfalse = in_ml mlfalse_name

  let mltrue_name = mk_name "true"
  let mltrue = in_ml mltrue_name

  (** Lists *)

  let list_name = mk_name "list"
  let list = PName list_name

  let nil_name = mk_name "[]"
  let nil = PName nil_name

  let cons_name = mk_name ~fixity:(Infix Level.InfixCons) "::"
  let cons = PName cons_name

  (** Comparison *)

  let mlorder_name = mk_name "order"
  let mlorder = in_ml mlorder_name

  let mlless_name = mk_name "less"
  let mlless = in_ml mlless_name

  let mlequal_name = mk_name "equal"
  let mlequal = in_ml mlequal_name

  let mlgreater_name = mk_name "greater"
  let mlgreater = in_ml mlgreater_name

  (** Option type *)

  let option_name = mk_name "option"
  let option = in_ml option_name

  let some_name = mk_name "Some"
  let some = in_ml some_name

  let none_name = mk_name "None"
  let none = in_ml none_name

  (** Builtin commands *)

  let equal_term_name = mk_name "equal_term"
  let equal_term = in_ml equal_term_name

  let equal_type_name = mk_name "equal_type"
  let equal_type = in_ml equal_type_name

  let coercible_ty_name = mk_name "coercible"
  let coercible_ty = in_ml coercible_ty_name

  let coercible_constructor_name = mk_name "Coercible"
  let coercible_constructor = in_ml coercible_constructor_name

  let convertible_name = mk_name "Convertible"
  let convertible = in_ml convertible_name

  let notcoercible_name = mk_name "NotCoercible"
  let notcoercible = in_ml notcoercible_name

  let coerce_name = mk_name "coerce"
  let coerce = in_ml coerce_name

  let hypotheses_name = mk_name "hypotheses"
  let hypotheses = in_ml hypotheses_name
end

(** Split a string into base and an optional numerical suffix, e.g., ["x42"],
   ["x₄₂"], and ["x4₂"] are split into [("x", Some 42)], while ["xy"] is split into [("xy",
   None)]. *)
let extract_suffix s =
  let rec ends_with c k i =
    k < 0 || (i >= 0 && c.[k] = s.[i] && ends_with c (k-1) (i-1))
  in
  let rec trailing_digit i = function
    | [] -> None
    | (c, d) :: lst ->
       let k = String.length c - 1 in
       if ends_with c k i
       then Some (d, i - k - 1)
       else trailing_digit i lst
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
      let digits =
        [("0",0); ("1",1); ("2",2); ("3",3); ("4",4); ("5",5); ("6",6); ("7",7); ("8",8); ("9",9);
         ("₀",0); ("₁",1); ("₂",2); ("₃",3); ("₄",4); ("₅",5); ("₆",6); ("₇",7); ("₈",8); ("₉",9)]
      in
      match trailing_digit i digits with
      | None ->
         if i = n - 1
         then (s, None)
         else (String.sub s 0 (i+1), Some (as_int 0 suffix))
      | Some (d, i) ->
         extract (d :: suffix) i
  in
  extract [] (n-1)

let equal {name=x;_} {name=y;_} = String.equal x y

module NameSet = Set.Make (
  struct
    type t_name = t
    type t = t_name
    let compare {name=x;_} {name=y;_} = String.compare x y
  end)

type set = NameSet.t

let set_empty = NameSet.empty

let set_add = NameSet.add

let set_mem = NameSet.mem

let prefer x y =
  match x.fixity with
  | Word | Prefix | Infix _ -> x
  | Anonymous _ -> y

let refresh forbidden ({name; fixity} as x) =
  let search fixity ?(k=0) s =
    let k = ref k in
    while set_mem {name = s ^ subscript !k; fixity} forbidden do incr k done;
    { name = s ^ subscript !k ; fixity }
  in
  match fixity with
  | Anonymous _ ->
     search Word ~k:0 "x"

  | (Word | Prefix | Infix _) ->
     if not (set_mem x forbidden) then
       x
     else
       let (s, k) = extract_suffix name in
       search fixity ?k s

module NameMap = Map.Make (
  struct
    type t_name = t
    type t = t_name
    let compare {name=x;_} {name=y;_} = String.compare x y
  end)

type 'a map = 'a NameMap.t

let map_empty = NameMap.empty

let map_add = NameMap.add

let map_find = NameMap.find

let map_map = NameMap.map

let map_fold = NameMap.fold

let index x ys =
  let rec fold k = function
    | [] -> None
    | y :: ys -> if equal x y then Some k else fold (k + 1) ys
  in
  fold 0 ys

let index_opt x ys =
  let rec fold k = function
    | [] -> None
    | None :: ys -> fold k ys
    | Some y :: ys -> if equal x y then Some k else fold (k + 1) ys
  in
  fold 0 ys

let level x ys = index x (List.rev ys)


(** Association lists indexed by de Bruijn indices *)
let print_debruijn xs k ppf =
  try
    let x = List.nth xs k in
    print x ppf
  with
  | Failure _ -> Format.fprintf ppf "[%d]" k

let print_debruijn_var = print_debruijn

let print_debruijn_meta = print_debruijn

module Json =
struct
  let name = function
    | {name=s; fixity=Anonymous k} -> Json.tuple [Json.String s; Json.Int k]
    | {name=s; fixity=(Word|Prefix|Infix _)} -> Json.String s
end
