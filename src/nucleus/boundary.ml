open Nucleus_types

(** Conversion between abstracted general and particular boundaries. *)

exception ConversionError

let rec convert f = function
  | NotAbstract a -> NotAbstract (f a)
  | Abstract (atm, abstr) -> Abstract (atm, convert f abstr)

let as_is_type_abstraction abstr =
  try
    Some
      (convert
         (function
          | BoundaryIsType () -> ()
          | BoundaryIsTerm _ | BoundaryEqType _ | BoundaryEqTerm _ -> raise ConversionError)
         abstr)
  with
  | ConversionError -> None

let as_is_term_abstraction abstr =
  try
    Some
      (convert
         (function
          | BoundaryIsTerm e -> e
          | BoundaryIsType _ | BoundaryEqType _ | BoundaryEqTerm _ -> raise ConversionError)
         abstr)
  with
  | ConversionError -> None

let from_is_type_abstraction abstr =
  convert (fun t -> BoundaryIsType t) abstr

let from_is_term_abstraction abstr =
  convert (fun t -> BoundaryIsTerm t) abstr
