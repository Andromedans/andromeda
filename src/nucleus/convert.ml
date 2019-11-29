open Nucleus_types

exception Convert_fail

let opt_fail = function
  | None -> raise Convert_fail
  | Some x -> x

let rec abstraction inst_u abstr_v converter u eq =
  match Invert.invert_abstractions inst_u Instantiate_bound.eq_type u eq with
  | None -> raise Convert_fail

  | Some (Stumps_NotAbstract (u, eq)) ->
     Mk.not_abstract (converter u eq)

  | Some (Stumps_Abstract ({atom_nonce=n; atom_type=t}, u, eq)) ->
     let v = abstraction inst_u abstr_v converter u eq in
     let v = Abstract.abstraction abstr_v n v in
     Mk.abstract (Nonce.name n) t v


let judgement sgn jdg eq =
  match jdg with
  | JudgementIsTerm e -> JudgementIsTerm (opt_fail (Form.form_is_term_convert_opt sgn e eq))
  | JudgementEqTerm eq' -> JudgementEqTerm (opt_fail (Form.form_eq_term_convert_opt eq' eq))
  | JudgementEqType _ -> raise Convert_fail
  | JudgementIsType _ -> raise Convert_fail

let term_abstraction sgn e eq =
  try
    let term sgn e eq = opt_fail (Form.form_is_term_convert_opt sgn e eq) in
    Some (abstraction Instantiate_bound.is_term Abstract.is_term (term sgn) e eq)
  with
  | Convert_fail -> None

let eq_term_abstraction eq1 eq2 =
  try
    let eq_term eq1 eq2 = opt_fail (Form.form_eq_term_convert_opt eq1 eq2) in
    Some (abstraction Instantiate_bound.eq_term Abstract.eq_term eq_term eq1 eq2)
  with
  | Convert_fail -> None

let judgement_abstraction sgn jdg eq =
  try
    Some (abstraction Instantiate_bound.judgement Abstract.judgement (judgement sgn) jdg eq)
  with
  | Convert_fail -> None
