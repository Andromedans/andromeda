(** An identifier uniquely determines an entity such as
    a let-bound name, an ML type, or a TT rule. *)

type t = { name : Name.t ; stamp : int }

let create =
  let stamp = ref 0 in
  fun x ->
    incr stamp ;
    let k = !stamp in
    (* We don't want an inconsistency just because someone actually used up 64
       bits worth of identifiers. *)
    assert (k > 0) ;
    { name = x;  stamp = k }

let name {name; _} = name

let equal {stamp=i;_} {stamp=j;_} = (i = j)

let compare {stamp=i;_} {stamp=j;_} = Pervasives.compare i j

module IdentMap = Map.Make(struct
                        type t_ident = t (* OCaml is a bit silly *)
                        type t = t_ident
                        let compare = compare
                      end)

type 'a map = 'a IdentMap.t

let empty = IdentMap.empty

let add = IdentMap.add

let find = IdentMap.find

let mem = IdentMap.mem

let map = IdentMap.map

let mapi = IdentMap.mapi

let bindings = IdentMap.bindings

let print ?parentheses {name;_} ppf = Name.print ?parentheses name ppf

module Json =
struct
  let ident {name=n; stamp=k; _} = Json.tuple [Name.Json.name n; Json.Int k]
end
