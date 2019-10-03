(** An identifier uniquely determines an entity such as
    a let-bound name, an ML type, or a TT rule. *)

type t = { path : Path.t ; stamp : int }

let create =
  let stamp = ref 0 in
  fun path ->
    incr stamp ;
    let k = !stamp in
    (* We don't want an inconsistency just because someone actually used up 64
       bits worth of identifiers. *)
    assert (k > 0) ;
    { path;  stamp = k }

let path {path; _} = path

let equal {stamp=i;_} {stamp=j;_} = (i = j)

let compare {stamp=i;_} {stamp=j;_} = Stdlib.compare i j

module IdentMap = Map.Make(struct
                        type nonrec t = t
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

let print ~opens ~parentheses {path;_} ppf = Path.print ~opens ~parentheses path ppf

module Json =
struct
  let ident {path; stamp=k; _} = Json.tuple [Path.Json.path path; Json.Int k]
end
