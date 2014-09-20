
type name = string

type debruijn = int


let next =
  (* Hide the counter in the closure *)
  let counter = ref 0  in
  fun () -> (counter := !counter + 1;
             string_of_int (!counter))
