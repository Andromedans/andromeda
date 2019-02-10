include Nucleus_types

module Signature = Signature

let meta_nonce = Meta.nonce
let eq_term_meta_eta_expanded = Meta.eq_term_meta_eta_expanded
let eq_type_meta_eta_expanded = Meta.eq_type_meta_eta_expanded
let is_term_meta_eta_expanded = Meta.is_term_meta_eta_expanded
let is_type_meta_eta_expanded = Meta.is_type_meta_eta_expanded
let form_eq_term_meta = Meta.form_eq_term_meta
let form_eq_type_meta = Meta.form_eq_type_meta
let form_is_term_meta = Meta.form_is_term_meta
let form_is_type_meta = Meta.form_is_type_meta


(** Exports from [Sanity] *)
let type_of_term = Sanity.type_of_term
let type_of_term_abstraction = Sanity.type_of_term_abstraction
let type_at_abstraction = Sanity.type_at_abstraction
let type_of_atom = Sanity.type_of_atom
let natural_type_eq = Sanity.natural_type_eq

let fresh_atom = Mk.fresh_atom
let fresh_is_type_meta = Mk.fresh_type_meta
let fresh_is_term_meta = Mk.fresh_term_meta
let fresh_eq_type_meta = Mk.fresh_eq_type_meta
let fresh_eq_term_meta = Mk.fresh_eq_term_meta

let alpha_equal_term = Alpha_equal.is_term
let alpha_equal_type = Alpha_equal.is_type
let alpha_equal_abstraction = Alpha_equal.abstraction

(** Construct judgements *)
let form_alpha_equal_term = Form.form_alpha_equal_term
let form_alpha_equal_type = Form.form_alpha_equal_type
let form_alpha_equal_abstraction = Form.form_alpha_equal_abstraction
let form_eq_term = Form.form_eq_term
let form_eq_type = Form.form_eq_type
let form_is_term = Form.form_is_term
let form_is_type = Form.form_is_type
let form_is_term_atom = Form.form_is_term_atom
let form_eq_term_convert = Form.form_eq_term_convert
let form_is_term_convert = Form.form_is_term_convert
let transitivity_type = Form.transitivity_type
let transitivity_term = Form.transitivity_term
let symmetry_type = Form.symmetry_type
let symmetry_term = Form.symmetry_term

(** Creation of rules of inference from judgements. *)
let form_rule_eq_term = Form_rule.form_rule_eq_term
let form_rule_eq_type = Form_rule.form_rule_eq_type
let form_rule_is_term = Form_rule.form_rule_is_term
let form_rule_is_type = Form_rule.form_rule_is_type

let abstract_boundary_eq_term = Abstract.boundary_eq_term_abstraction
let abstract_boundary_eq_type = Abstract.boundary_eq_type_abstraction
let abstract_boundary_is_term = Abstract.boundary_is_term_abstraction
let abstract_boundary_is_type = Abstract.boundary_is_type_abstraction
let abstract_eq_term = Abstract.eq_term_abstraction
let abstract_eq_type = Abstract.eq_type_abstraction
let abstract_is_term = Abstract.is_term_abstraction
let abstract_is_type = Abstract.is_type_abstraction
let abstract_not_abstract = Abstract.not_abstract

let invert_eq_term_abstraction = Invert.invert_eq_term_abstraction
let invert_eq_type_abstraction = Invert.invert_eq_type_abstraction
let invert_is_type_abstraction = Invert.invert_is_type_abstraction
let invert_is_term_abstraction = Invert.invert_is_term_abstraction
let invert_eq_term = Invert.invert_eq_term
let invert_eq_type = Invert.invert_eq_type
let invert_is_term = Invert.invert_is_term
let invert_is_type = Invert.invert_is_type
let as_not_abstract = Invert.as_not_abstract
let atom_name = Invert.atom_name


let context_is_type_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.is_type
let context_is_term_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.is_term
let context_eq_type_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.eq_type
let context_eq_term_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.eq_term

let apply_eq_term_abstraction = Apply_abstraction.apply_eq_term_abstraction
let apply_eq_type_abstraction = Apply_abstraction.apply_eq_type_abstraction
let apply_is_term_abstraction = Apply_abstraction.apply_is_term_abstraction
let apply_is_type_abstraction = Apply_abstraction.apply_is_type_abstraction

let occurs_abstraction assumptions_u a abstr =
  let asmp = Collect_assumptions.abstraction assumptions_u abstr in
  Assumption.mem_atom a.atom_nonce asmp

let occurs_is_type_abstraction = occurs_abstraction Collect_assumptions.is_type
let occurs_is_term_abstraction = occurs_abstraction Collect_assumptions.is_term
let occurs_eq_type_abstraction = occurs_abstraction Collect_assumptions.eq_type
let occurs_eq_term_abstraction = occurs_abstraction Collect_assumptions.eq_term

let congruence_term_constructor = Congruence.congruence_term_constructor
let congruence_type_constructor = Congruence.congruence_type_constructor

let print_is_term = Nucleus_print.is_term
let print_is_type = Nucleus_print.is_type
let print_eq_term = Nucleus_print.eq_term
let print_eq_type = Nucleus_print.eq_type
let print_is_term_abstraction = Nucleus_print.is_term_abstraction
let print_is_type_abstraction = Nucleus_print.is_type_abstraction
let print_eq_term_abstraction = Nucleus_print.eq_term_abstraction
let print_eq_type_abstraction = Nucleus_print.eq_type_abstraction
let print_error = Nucleus_print.error

module Json = Nucleus_json
