let empty : Rule.primitive Ident.map = Ident.empty

let add_rule c rule (sgn : Rule.primitive Ident.map) = assert (not (Ident.mem c sgn)) ; Ident.add c rule sgn

let lookup_rule c (sgn : Rule.primitive Ident.map) = Ident.find c sgn
