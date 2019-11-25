module type S =
  sig
    type key

    val key_eq : key -> key -> bool

    val print_key : key -> Format.formatter -> unit

    type 'a t

    val empty : 'a t

    (** [lookup x s] returns the value bound to [x] in [s] *)
    val lookup : key -> 'a t -> 'a

    (** [fresh v s] returns a new key [x] and store [s'] such that the bindings in [s] are in [s'], and [x] is bound to [v] in [s'] *)
    val fresh : 'a -> 'a t -> key * 'a t

    (** [update x v s] when [x] is already bound in [s] returns [s'] in which it is bound to [v] *)
    val update : key -> 'a -> 'a t -> 'a t
  end

module Store =
struct
  type key = int

  let key_eq x y = (x == y)

  let print_key x ppf = Format.fprintf ppf "%d" x

  module KeyMap = Map.Make (struct
                             type t = key
                             let compare = Stdlib.compare
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
end

module Ref = Store
module Dyn = Store
