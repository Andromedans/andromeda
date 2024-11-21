open Nucleus_types

let empty : primitive Ident.map = Ident.empty

let add_rule c rule (sgn : primitive Ident.map) = assert (not (Ident.mem c sgn)) ; Ident.add c rule sgn

let lookup_rule c (sgn : primitive Ident.map) = Ident.find c sgn
