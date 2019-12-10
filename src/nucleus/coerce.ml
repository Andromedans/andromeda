open Nucleus_types

(** Conversion from abstracted general judgements to abstracted particular judgements. *)

exception ConversionError

let rec convert f = function
  | NotAbstract a -> NotAbstract (f a)
  | Abstract (x, t, abstr) -> Abstract (x, t, convert f abstr)

let as_is_type = function
  | JudgementIsType t -> Some t
  | JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _ -> None

let as_is_term = function
  | JudgementIsTerm e -> Some e
  | JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _ -> None

let as_eq_type = function
  | JudgementEqType eq -> Some eq
  | JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _ -> None

let as_eq_term = function
  | JudgementEqTerm eq -> Some eq
  | JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _ -> None

let as_is_type_abstraction abstr =
  try
    Some
      (convert
         (function
          | JudgementIsType t -> t
          | JudgementIsTerm _ | JudgementEqType _ | JudgementEqTerm _ -> raise ConversionError)
         abstr)
  with
  | ConversionError -> None

let as_is_term_abstraction abstr =
  try
    Some
      (convert
         (function
          | JudgementIsTerm e -> e
          | JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _ -> raise ConversionError)
         abstr)
  with
  | ConversionError -> None

let as_eq_type_abstraction abstr =
  try
    Some
      (convert
         (function
          | JudgementEqType eq -> eq
          | JudgementIsType _ | JudgementIsTerm _ | JudgementEqTerm _ -> raise ConversionError)
         abstr)
  with
  | ConversionError -> None

let as_eq_term_abstraction abstr =
  try
    Some
      (convert
         (function
          | JudgementEqTerm eq -> eq
          | JudgementIsType _ | JudgementIsTerm _ | JudgementEqType _ -> raise ConversionError)
         abstr)
  with
  | ConversionError -> None

let from_is_type_abstraction abstr =
  convert (fun t -> JudgementIsType t) abstr

let from_is_term_abstraction abstr =
  convert (fun t -> JudgementIsTerm t) abstr

let from_eq_type_abstraction abstr =
  convert (fun t -> JudgementEqType t) abstr

let from_eq_term_abstraction abstr =
  convert (fun t -> JudgementEqTerm t) abstr

(** Conversion to an argument *)
let rec to_argument = function
  | NotAbstract jdg -> Arg_NotAbstract jdg
  | Abstract (x, _, abstr) -> Arg_Abstract (x, to_argument abstr)

let convert_rule f rl =
  let rec fold = function
    | Conclusion concl ->
       begin match f concl with
       | Some concl -> Conclusion concl
       | None -> raise ConversionError
       end

    | Premise (mv, rl) -> Premise (mv, fold rl)
  in
  try
    Some (fold rl)
  with
  | ConversionError -> None

let as_is_type_rule = convert_rule as_is_type
let as_is_term_rule = convert_rule as_is_term
let as_eq_type_rule = convert_rule as_eq_type
let as_eq_term_rule = convert_rule as_eq_term
