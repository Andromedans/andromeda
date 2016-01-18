
type key = int

let key_eq x y = (x == y)

let print_key x ppf = Format.fprintf ppf "%d" x

module KeyMap = Map.Make (struct
    type t = key
    let compare = compare
  end)

type 'a t = {store : 'a KeyMap.t; counter : int}

let empty = {store=KeyMap.empty; counter=0}

let lookup x s =
  KeyMap.find x s.store

let fresh v {store;counter} =
  let x = counter in
  let store = KeyMap.add x v store in
  x,{store;counter=counter+1}

let update x v s =
  {s with store = KeyMap.add x v s.store}

