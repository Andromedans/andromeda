type name = string

type debruijn = int

let next =
  (* Hide the counter in the closure *)
  let counter = ref 0  in
  fun () -> (incr counter ; string_of_int (!counter))
