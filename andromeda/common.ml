
type name = string

type debruijn = int

let counter = ref 0
let next() = (counter := !counter + 1;
              string_of_int (!counter))
