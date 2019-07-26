open Nucleus_types

let apply_abstraction inst_u sgn abstr e0 =
  match abstr with
  | NotAbstract _ -> Error.raise AbstractionExpected
  | Abstract ({atom_type=t;_}, abstr) ->
     begin match Alpha_equal.is_type t (Sanity.type_of_term sgn e0) with
     | false -> Error.raise InvalidSubstitution
     | true ->  Instantiate_bound.abstraction inst_u e0 abstr
     end

let apply_is_type_abstraction sgn abstr e0 =
  apply_abstraction Instantiate_bound.is_type sgn abstr e0

let apply_is_term_abstraction sgn abstr e0 =
  apply_abstraction Instantiate_bound.is_term sgn abstr e0

let apply_eq_type_abstraction sgn abstr e0 =
  apply_abstraction Instantiate_bound.eq_type sgn abstr e0

let apply_eq_term_abstraction sgn abstr e0 =
  apply_abstraction Instantiate_bound.eq_term sgn abstr e0

let apply_judgement_abstraction sgn abstr e0 =
  apply_abstraction Instantiate_bound.judgement sgn abstr e0

(* Apply [abstr] to a list of terms of length equal to the abstraction level
   of [abstr]. Verify that the terms to be substituted match the types on the
   abstraction. *)
let rec fully_apply_abstraction inst_u sgn abstr = function
  | [] ->
     begin match abstr with
     | NotAbstract x -> x
     | Abstract _ -> Error.raise TooFewArguments
     end
  | arg :: args ->
     let abstr = apply_abstraction inst_u sgn abstr arg in
     fully_apply_abstraction inst_u sgn abstr args
