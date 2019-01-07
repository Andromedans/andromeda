open Nucleus_types

let empty =
  { is_type = Ident.empty
  ; is_term = Ident.empty
  ; eq_type = Ident.empty
  ; eq_term = Ident.empty
  }

let add_new c rule map = assert (not (Ident.mem c map)) ; Ident.add c rule map

let add_rule_is_type c rule sgn = { sgn with is_type = add_new c rule sgn.is_type }
let add_rule_is_term c rule sgn = { sgn with is_term = add_new c rule sgn.is_term }
let add_rule_eq_type c rule sgn = { sgn with eq_type = add_new c rule sgn.eq_type }
let add_rule_eq_term c rule sgn = { sgn with eq_term = add_new c rule sgn.eq_term }

let lookup_rule_is_type c sgn = Ident.find c sgn.is_type
let lookup_rule_is_term c sgn = Ident.find c sgn.is_term
let lookup_rule_eq_type c sgn = Ident.find c sgn.eq_type
let lookup_rule_eq_term c sgn = Ident.find c sgn.eq_term
