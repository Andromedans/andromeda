let empty : Rule.t Ident.map = Ident.empty

let add_rule c rule (sgn : Rule.t Ident.map) = assert (not (Ident.mem c sgn)) ; Ident.add c rule sgn

let lookup_rule c (sgn : Rule.t Ident.map) = Ident.find c sgn
