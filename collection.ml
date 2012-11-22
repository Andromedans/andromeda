(** A very simple datatype for representing unordered collections. *)

(** We need a datatype which allows us to quickly join collections of data, and to
    traverse the collection in an arbitrary order. Trees serve the purpose nicely. *)
type 'a collection =
  | Datum of 'a
  | Cons of 'a collection list

let empty = Cons []

let rec fold f a = function
  | Datum x -> f a x
  | Cons of lst -> List.fold_left (fold f) a lst
