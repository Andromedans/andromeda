include Nucleus_types

module Signature = Signature

let meta_nonce = Meta.nonce
let judgement_meta_eta_expanded = Meta.judgement_meta_eta_expanded

let form_is_term_meta = Meta.form_is_term_meta
let form_is_type_meta = Meta.form_is_type_meta


(** Exports from [Sanity] *)
let type_of_term = Sanity.type_of_term
let type_of_term_abstraction = Sanity.type_of_term_abstraction
let type_at_abstraction = Sanity.type_at_abstraction
let type_of_atom = Sanity.type_of_atom
let natural_type_eq = Sanity.natural_type_eq

let check_judgement_boundary_abstraction = Check.judgement_boundary_abstraction

let fresh_atom = Mk.fresh_atom
let fresh_is_type_meta = Mk.fresh_type_meta
let fresh_is_term_meta = Mk.fresh_term_meta
let fresh_eq_type_meta = Mk.fresh_eq_type_meta
let fresh_eq_term_meta = Mk.fresh_eq_term_meta

let fresh_judgement_meta = Mk.fresh_judgement_meta

let alpha_equal_term = Alpha_equal.is_term
let alpha_equal_type = Alpha_equal.is_type
let alpha_equal_abstraction = Alpha_equal.abstraction

let alpha_equal_judgement = Alpha_equal.judgement
let alpha_equal_boundary = Alpha_equal.boundary


(** Construct judgements *)
let form_alpha_equal_term = Form.form_alpha_equal_term
let form_alpha_equal_type = Form.form_alpha_equal_type
let form_alpha_equal_abstraction = Form.form_alpha_equal_abstraction
let form_rap = Form.form_rap
let rap_apply = Form.rap_apply
let rap_boundary = Form.rap_boundary

let form_is_term_atom = Form.form_is_term_atom
let form_eq_term_convert = Form.form_eq_term_convert
let form_is_term_convert = Form.form_is_term_convert
let transitivity_type = Form.transitivity_type
let transitivity_term = Form.transitivity_term
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

(* let abstract_boundary_eq_term = Abstract.boundary_eq_term_abstraction *)
(* let abstract_boundary_eq_type = Abstract.boundary_eq_type_abstraction *)
(* let abstract_boundary_is_term = Abstract.boundary_is_term_abstraction *)
(* let abstract_boundary_is_type = Abstract.boundary_is_type_abstraction *)

let abstract_boundary = Abstract.boundary_abstraction

(* let abstract_eq_term = Abstract.eq_term_abstraction *)
(* let abstract_eq_type = Abstract.eq_type_abstraction *)
let abstract_is_term = Abstract.is_term_abstraction
(* let abstract_is_type = Abstract.is_type_abstraction *)

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

let as_is_type_abstraction = Judgement.as_is_type_abstraction
let as_is_term_abstraction = Judgement.as_is_term_abstraction
let as_eq_type_abstraction = Judgement.as_eq_type_abstraction
let as_eq_term_abstraction = Judgement.as_eq_term_abstraction

let as_is_type = Judgement.as_is_type
let as_is_term = Judgement.as_is_term
let as_eq_type = Judgement.as_eq_type
let as_eq_term = Judgement.as_eq_term


let context_is_type_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.is_type
let context_is_term_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.is_term
let context_eq_type_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.eq_type
let context_eq_term_abstraction = Collect_assumptions.context_of_abstraction Collect_assumptions.eq_term

let apply_eq_term_abstraction = Apply_abstraction.apply_eq_term_abstraction
let apply_eq_type_abstraction = Apply_abstraction.apply_eq_type_abstraction
let apply_is_term_abstraction = Apply_abstraction.apply_is_term_abstraction
let apply_is_type_abstraction = Apply_abstraction.apply_is_type_abstraction
let apply_judgement_abstraction = Apply_abstraction.apply_judgement_abstraction

let occurs_abstraction assumptions_u a abstr =
  let asmp = Collect_assumptions.abstraction assumptions_u abstr in
  Assumption.mem_atom a.atom_nonce asmp

let occurs_is_type_abstraction = occurs_abstraction Collect_assumptions.is_type
let occurs_is_term_abstraction = occurs_abstraction Collect_assumptions.is_term
let occurs_eq_type_abstraction = occurs_abstraction Collect_assumptions.eq_type
let occurs_eq_term_abstraction = occurs_abstraction Collect_assumptions.eq_term
let occurs_judgement_abstraction = occurs_abstraction Collect_assumptions.judgement

let convert_term_abstraction = Convert.term_abstraction
let convert_eq_term_abstraction = Convert.eq_term_abstraction
let convert_judgement_abstraction = Convert.judgement_abstraction

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
let print_judgement_abstraction = Nucleus_print.judgement_abstraction
let print_boundary_abstraction = Nucleus_print.boundary_abstraction
let print_error = Nucleus_print.error

let name_of_judgement = Nucleus_print.name_of_judgement
let name_of_boundary = Nucleus_print.name_of_boundary

module Json = Nucleus_json
