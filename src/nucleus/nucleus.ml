include Nucleus_types

module Signature = Signature

let form_meta = Meta.form_meta

let meta_nonce {meta_nonce;_} = meta_nonce
let meta_boundary {meta_boundary;_} = meta_boundary

(** Exposing the inner structure (safely) *)
let expose_is_term e = e
let expose_is_type t = t
let expose_eq_type eq = eq
let expose_eq_term eq = eq
let expose_judgement jdg = jdg
let expose_rule rl = rl

(** Exports from [Sanity] *)
let type_of_term = Sanity.type_of_term
let type_of_term_abstraction = Sanity.type_of_term_abstraction
let type_at_abstraction = Sanity.type_at_abstraction
let type_of_atom = Sanity.type_of_atom
let natural_type_eq = Sanity.natural_type_eq

let check_judgement_boundary_abstraction = Check.judgement_boundary_abstraction

let fresh_atom = Mk.fresh_atom

let alpha_equal_term = Alpha_equal.is_term
let alpha_equal_type = Alpha_equal.is_type
let alpha_equal_atom = Alpha_equal.is_atom
let alpha_equal_abstraction = Alpha_equal.abstraction

let alpha_equal_judgement = Alpha_equal.judgement
let alpha_equal_boundary = Alpha_equal.boundary

(** Construct judgements *)
let form_alpha_equal_term = Form.form_alpha_equal_term
let form_alpha_equal_type = Form.form_alpha_equal_type
let form_alpha_equal_abstraction = Form.form_alpha_equal_abstraction

(** Construction of rule applications *)
let form_constructor_rap = Form.form_constructor_rap
let form_meta_rap = Form.form_meta_rap
let form_is_type_rap = Form.form_is_type_rap
let form_is_term_rap = Form.form_is_term_rap
let form_eq_type_rap = Form.form_eq_type_rap
let form_eq_term_rap = Form.form_eq_term_rap

let form_derivation_rap = Form.form_derivation_rap
let rule_as_derivation = Form.rule_as_derivation

(** Miscelaneous constructions *)
let form_is_term_atom = Form.form_is_term_atom
let form_eq_term_convert = Form.form_eq_term_convert
let form_is_term_convert = Form.form_is_term_convert

let reflexivity_type = Form.reflexivity_type
let reflexivity_term = Form.reflexivity_term
let reflexivity_judgement_abstraction = Form.reflexivity_judgement_abstraction

let transitivity_type = Form.transitivity_type
let transitivity_term = Form.transitivity_term
let transitivity_term' = Form.transitivity_term'
let symmetry_type = Form.symmetry_type
let symmetry_term = Form.symmetry_term

(** Form a boundary *)
let form_is_type_boundary = Form.form_is_type_boundary
let form_is_term_boundary = Form.form_is_term_boundary
let form_eq_type_boundary = Form.form_eq_type_boundary
let form_eq_term_boundary = Form.form_eq_term_boundary
let form_is_term_boundary_abstraction = Form.form_is_term_boundary_abstraction

(** Creation of rules of inference from judgements. *)
let form_rule = Form_rule.form_rule
let form_derivation = Form_rule.form_derivation

let abstract_boundary = Abstract.boundary_abstraction
let abstract_is_term = Abstract.is_term_abstraction
let abstract_is_type = Abstract.is_type_abstraction
let abstract_eq_type = Abstract.eq_type_abstraction
let abstract_eq_term = Abstract.eq_term_abstraction

let abstract_judgement = Abstract.judgement_abstraction

let abstract_not_abstract = Abstract.not_abstract

let invert_eq_term_abstraction = Invert.invert_eq_term_abstraction
let invert_eq_type_abstraction = Invert.invert_eq_type_abstraction
let invert_is_type_abstraction = Invert.invert_is_type_abstraction
let invert_is_term_abstraction = Invert.invert_is_term_abstraction
let invert_judgement_abstraction = Invert.invert_judgement_abstraction

let invert_is_term = Invert.invert_is_term
let invert_is_type = Invert.invert_is_type
let invert_eq_type = Invert.invert_eq_type
let invert_eq_term = Invert.invert_eq_term

let invert_eq_term_boundary = Invert.invert_eq_term_boundary

let invert_is_type_boundary_abstraction = Invert.invert_is_type_boundary_abstraction
let invert_is_term_boundary_abstraction = Invert.invert_is_term_boundary_abstraction
let invert_eq_type_boundary_abstraction = Invert.invert_eq_type_boundary_abstraction
let invert_eq_term_boundary_abstraction = Invert.invert_eq_term_boundary_abstraction

let invert_boundary_abstraction = Invert.invert_boundary_abstraction

let as_not_abstract = Invert.as_not_abstract
let atom_name = Invert.atom_name
let atom_nonce {atom_nonce;_} = atom_nonce

(** Coercions *)

let as_is_type_abstraction = Coerce.as_is_type_abstraction
let as_is_term_abstraction = Coerce.as_is_term_abstraction
let as_eq_type_abstraction = Coerce.as_eq_type_abstraction
let as_eq_term_abstraction = Coerce.as_eq_term_abstraction

let as_is_type = Coerce.as_is_type
let as_is_term = Coerce.as_is_term
let as_eq_type = Coerce.as_eq_type
let as_eq_term = Coerce.as_eq_term

let from_is_type_abstraction = Coerce.from_is_type_abstraction
let from_is_term_abstraction = Coerce.from_is_term_abstraction
let from_eq_type_abstraction = Coerce.from_eq_type_abstraction
let from_eq_term_abstraction = Coerce.from_eq_term_abstraction

let as_is_type_rule = Coerce.as_is_type_rule
let as_is_term_rule = Coerce.as_is_term_rule
let as_eq_type_rule = Coerce.as_eq_type_rule
let as_eq_term_rule = Coerce.as_eq_term_rule

let as_is_type_boundary_abstraction = Coerce.as_is_type_boundary_abstraction
let as_is_term_boundary_abstraction = Coerce.as_is_term_boundary_abstraction
let as_eq_type_boundary_abstraction = Coerce.as_eq_type_boundary_abstraction
let as_eq_term_boundary_abstraction = Coerce.as_eq_term_boundary_abstraction

let as_is_type_boundary = Coerce.as_is_type_boundary
let as_is_term_boundary = Coerce.as_is_term_boundary
let as_eq_type_boundary = Coerce.as_eq_type_boundary
let as_eq_term_boundary = Coerce.as_eq_term_boundary

let from_is_type_boundary_abstraction = Coerce.from_is_type_boundary_abstraction
let from_is_term_boundary_abstraction = Coerce.from_is_term_boundary_abstraction
let from_eq_type_boundary_abstraction = Coerce.from_eq_type_boundary_abstraction
let from_eq_term_boundary_abstraction = Coerce.from_eq_term_boundary_abstraction

let context_is_type_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.is_type
let context_is_term_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.is_term
let context_eq_type_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.eq_type
let context_eq_term_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.eq_term

let apply_eq_term_abstraction = Apply_abstraction.apply_eq_term_abstraction
let apply_eq_type_abstraction = Apply_abstraction.apply_eq_type_abstraction
let apply_is_term_abstraction = Apply_abstraction.apply_is_term_abstraction
let apply_is_type_abstraction = Apply_abstraction.apply_is_type_abstraction
let apply_judgement_abstraction = Apply_abstraction.apply_judgement_abstraction

let apply_eq_term_boundary_abstraction = Apply_abstraction.apply_eq_term_boundary_abstraction
let apply_eq_type_boundary_abstraction = Apply_abstraction.apply_eq_type_boundary_abstraction
let apply_is_term_boundary_abstraction = Apply_abstraction.apply_is_term_boundary_abstraction
let apply_is_type_boundary_abstraction = Apply_abstraction.apply_is_type_boundary_abstraction
let apply_boundary_abstraction = Apply_abstraction.apply_boundary_abstraction

let occurs_abstraction assumptions_u a abstr =
  let asmp = Collect_assumptions.abstraction assumptions_u abstr in
  Assumption.mem_free_var a.atom_nonce asmp

let occurs_is_type_abstraction = occurs_abstraction Collect_assumptions.is_type
let occurs_is_term_abstraction = occurs_abstraction Collect_assumptions.is_term
let occurs_eq_type_abstraction = occurs_abstraction Collect_assumptions.eq_type
let occurs_eq_term_abstraction = occurs_abstraction Collect_assumptions.eq_term
let occurs_judgement_abstraction = occurs_abstraction Collect_assumptions.judgement

let convert_term = Form.form_is_term_convert_opt
let convert_eq_term = Form.form_eq_term_convert_opt
let convert_term_abstraction = Convert.term_abstraction
let convert_eq_term_abstraction = Convert.eq_term_abstraction
let convert_judgement_abstraction = Convert.judgement_abstraction

let congruence_judgement = Congruence.form_judgement
let congruence_is_type = Congruence.form_is_type
let congruence_is_term = Congruence.form_is_term


let print_is_term = Nucleus_print.is_term
let print_is_type = Nucleus_print.is_type
let print_eq_term = Nucleus_print.eq_term
let print_eq_type = Nucleus_print.eq_type
let print_is_term_abstraction = Nucleus_print.is_term_abstraction
let print_is_type_abstraction = Nucleus_print.is_type_abstraction
let print_eq_term_abstraction = Nucleus_print.eq_term_abstraction
let print_eq_type_abstraction = Nucleus_print.eq_type_abstraction
let print_judgement_abstraction = Nucleus_print.judgement_abstraction
let print_boundary_abstraction = Nucleus_print.boundary_abstraction
let print_derivation = Nucleus_print.derivation
let print_error = Nucleus_print.error

let name_of_judgement = Nucleus_print.name_of_judgement
let name_of_boundary = Nucleus_print.name_of_boundary

module Json = Nucleus_json
