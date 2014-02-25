(** Abstract syntax of input files. *)

(** Abstract syntax of terms as given by the user. *)
type term = term' * Common.position
and term' =
  | Var of Common.variable
  | Num of int
  | Universe of universe
  | Lambda of Common.variable * term option * term
  | Pi of Common.variable * term * term
  | App of term * term
  | Sigma of Common.variable * term * term
  | Pair of term * term
  | Proj of string * term
  | Ascribe of term * term      (* Technically unnecessary for Brazil *)
  | Handle of term * handler list
  | Equiv of eqsort * term * term * term
  | J of eqsort * term * term * term
  | Refl of eqsort * term

and universe =
  | Type
  | Fib

and eqsort =
  | Ju
  | Pr

and handler = term

type toplevel = toplevel' * Common.position
and toplevel' =
  | TopDef of Common.variable * term
  | TopParam of Common.variable list * term
  | TopHandler of handler list
  | Context
  | Help
  | Quit

let rec string_of_term (term, loc) =
  match term with
  | Var x -> x
  | Num n -> string_of_int n
  | Universe u -> string_of_universe u
  | Lambda(x,None,t2) ->
      "Lambda(" ^ x ^ "," ^ "_" ^ "," ^ (string_of_term t2) ^ ")"
  | Lambda(x,Some t1,t2) ->
      "Lambda(" ^ x ^ "," ^ (string_of_terms [t1;t2]) ^ ")"
  | Pi(x,t1,t2) ->
      "Pi(" ^ x ^ "," ^ (string_of_terms [t1;t2]) ^ ")"
  | Sigma(x,t1,t2) ->
      "Sigma(" ^ x ^ "," ^ (string_of_terms [t1;t2]) ^ ")"
  | App(t1,t2) ->
      "App(" ^ (string_of_terms [t1;t2]) ^ ")"
  | Pair(t1,t2) ->
      "Pair(" ^ (string_of_terms [t1;t2]) ^ ")"
  | Proj(s1, t2) ->
      "Proj(\"" ^ s1 ^ "\"," ^ (string_of_term t2) ^ ")"
  | Ascribe(t1,t2) ->
      "Ascribe(" ^ (string_of_terms [t1;t2]) ^ ")"
  | Handle(term, cases) ->
      "Handle(" ^ (string_of_term term) ^ "," ^
      string_of_terms cases ^ ")"
  | Equiv(o,t1,t2,t3) ->
      "Equiv(" ^ (string_of_eqsort o) ^ "," ^ string_of_terms [t1; t2; t3] ^ ")"
  | J(o,t1,t2,t3) ->
      "J(" ^ (string_of_eqsort o) ^ "," ^ string_of_terms [t1; t2; t3] ^ ")"
  | Refl(o,t) ->
      "J(" ^ (string_of_eqsort o) ^ "," ^ string_of_term t ^ ")"


and string_of_universe = function
  | Type -> "Type"
  | Fib -> "Fib"

and string_of_eqsort = function
  | Ju -> "Ju"
  | Pr -> "Pr"


and string_of_terms terms = (String.concat "," (List.map string_of_term terms))


let print term = print_endline (string_of_term term)

