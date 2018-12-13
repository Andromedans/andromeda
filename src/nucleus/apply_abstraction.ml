open Jdg_typedefs

let apply_abstraction inst_u sgn abstr e0 =
  match abstr with
  | NotAbstract _ -> TT_error.raise AbstractionExpected
  | Abstract (x, t, abstr) ->
     begin match TT_alpha_equal.ty t (Sanity.type_of_term sgn e0) with
     | false -> TT_error.raise InvalidSubstitution
     | true ->  TT_instantiate.abstraction inst_u e0 abstr
     end

let apply_is_type_abstraction sgn abstr e0 =
  apply_abstraction TT_instantiate.ty sgn abstr e0

let apply_is_term_abstraction sgn abstr e0 =
  apply_abstraction TT_instantiate.term sgn abstr e0

let apply_eq_type_abstraction sgn abstr e0 =
  apply_abstraction TT_instantiate.eq_type sgn abstr e0

let apply_eq_term_abstraction sgn abstr e0 =
  apply_abstraction TT_instantiate.eq_term sgn abstr e0

(* Apply [abstr] to a list of terms of length equal to the abstraction level
   of [abstr]. Verify that the terms to be substituted match the types on the
   abstraction. *)
let rec fully_apply_abstraction inst_u sgn abstr = function
  | [] ->
     begin match abstr with
     | NotAbstract eq -> eq
     | Abstract _ -> TT_error.raise TooFewArguments
     end
  | arg :: args ->
     let abstr = apply_abstraction inst_u sgn abstr arg in
     fully_apply_abstraction inst_u sgn abstr args
