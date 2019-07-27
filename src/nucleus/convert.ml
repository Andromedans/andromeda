open Nucleus_types

exception Convert_fail

let opt_fail = function
  | None -> raise Convert_fail
  | Some x -> x

let rec abstraction converter jdg eq =
  match jdg, eq with

  | NotAbstract jdg, NotAbstract eq ->
     NotAbstract (converter jdg eq)

  | Abstract ({atom_type=u;_} as x, jdg), Abstract ({atom_type=v;_}, eq) ->
     begin match Alpha_equal.is_type u v with
     | false -> raise Convert_fail
     | true -> Abstract (x, abstraction converter jdg eq)
     end

  | NotAbstract _, Abstract _
  | Abstract _, NotAbstract _ -> raise Convert_fail

let term sgn e eq = opt_fail (Form.form_is_term_convert_opt sgn e eq)

let eq_term eq1 eq2 = opt_fail (Form.form_eq_term_convert_opt eq1 eq2)

let judgement sgn jdg eq =
  match jdg with
  | JudgementIsTerm e -> JudgementIsTerm (opt_fail (Form.form_is_term_convert_opt sgn e eq))
  | JudgementEqTerm eq' -> JudgementEqTerm (opt_fail (Form.form_eq_term_convert_opt eq' eq))
  | JudgementEqType _ -> raise Convert_fail
  | JudgementIsType _ -> raise Convert_fail

let term_abstraction sgn e eq =
  try
    Some (abstraction (term sgn) e eq)
  with
  | Convert_fail -> None

let eq_term_abstraction eq1 eq2 =
  try
    Some (abstraction eq_term eq1 eq2)
  with
  | Convert_fail -> None

let judgement_abstraction sgn jdg eq =
  try
    Some (abstraction (judgement sgn) jdg eq)
  with
  | Convert_fail -> None
