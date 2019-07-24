open Nucleus_types

(** Conversion from abstracted general judgements to abstracted particular judgements. *)

exception ConversionError

let rec convert f = function
  | NotAbstract a -> NotAbstract (f a)
  | Abstract (atm, abstr) -> Abstract (atm, convert f abstr)

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

let from_is_type_abstraction abstr =
  convert (fun t -> JudgementIsType t) abstr

let from_is_term_abstraction abstr =
  convert (fun t -> JudgementIsTerm t) abstr

let from_eq_type_abstraction abstr =
  convert (fun t -> JudgementEqType t) abstr

let from_eq_term_abstraction abstr =
  convert (fun t -> JudgementEqTerm t) abstr
