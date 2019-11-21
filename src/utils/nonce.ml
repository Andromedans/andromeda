type t =
  { name : Name.t ;
    stamp : int ;
    mutable print : int option (* the printed index, if any *)
  }

let create =
  let stamp = ref 0 in
  function n ->
    incr stamp ;
    let k = !stamp in
    assert (k > 0) ;
    { name = n ; stamp = k ; print = None }

let name {name; _} = name

let equal {stamp=i;_} {stamp=j;_} = (i = j)

let compare {stamp=i;_} {stamp=j;_} =
  if i < j then -1 else if i > j then 1 else 0

module NonceMap = Map.Make (struct
                    type t_nonce = t
                    type t = t_nonce
                    let compare = compare
                  end)

type 'a map = 'a NonceMap.t

let map_empty = NonceMap.empty

let map_add = NonceMap.add

let map_find = NonceMap.find

let map_is_empty = NonceMap.is_empty

let map_mem = NonceMap.mem

let map_union = NonceMap.union

let map_remove = NonceMap.remove

let map_bindings = NonceMap.bindings

let map_for_all = NonceMap.for_all

module NonceSet = Set.Make (struct
                    type t_nonce = t
                    type t = t_nonce
                    let compare = compare
                  end)

type set = NonceSet.t

let set_empty = NonceSet.empty

let set_is_empty = NonceSet.is_empty

let set_of_list = NonceSet.of_list

let set_add = NonceSet.add

let set_mem = NonceSet.mem

(* We expect that most nonces are never printed. Therefore, for the purposes of
   printing, we keep a counter and remember how each one got printed. *)
let fresh_print_index =
  let k = ref (-1) in
  fun () -> incr k ; !k

let print ~parentheses m ppf =
  let k =
    match m.print with
    | Some k -> k
    | None ->
       let k = fresh_print_index () in
       m.print <- Some k ;
       k
  in
  match m.name with
  | {Name.name=s; Name.fixity=Name.Word} ->
     Format.fprintf ppf "%s%s" s (Name.subscript k)

  | {Name.name=_; Name.fixity=Name.Anonymous j} ->
     Format.fprintf ppf "_anon%d%s" j (Name.subscript k)

  | {Name.name=s; Name.fixity=(Name.Prefix|Name.Infix _)} ->
     if parentheses then
       Format.fprintf ppf "( %s%s )" s (Name.subscript k)
     else
       Format.fprintf ppf "%s%s" s (Name.subscript k)

module Json =
struct
  let nonce {name=n; stamp=k; _} = Json.tuple [Name.Json.name n; Json.Int k]

  let map s = Json.List (List.map (fun (x, _) -> nonce x) (NonceMap.bindings s))
end
