(** Abstract syntax of input files. *)

(** Abstract syntax of terms as given by the user. *)
type term = term' * Common.position
and term' =
  | Var of Common.variable
  | Type
  | Lambda of Common.variable * term option * term
  | Pi of Common.variable * term * term
  | App of term * term
  | Sigma of Common.variable * term * term
  | Pair of term * term
  | Proj of string * term
  | Ascribe of term * term
  | Operation of operation_tag * term list
  | Handle of term * handler

and operation_tag =
  | Inhabit
  | Equiv

  (*
and computation = computation' * Common.position
and computation' =
  | Return of term
  | Let of Common.variable * term * computation
and handler_body = computation
  *)
and handler_body = term

and handler =
   (operation_tag * term list * handler_body) list

type toplevel = toplevel' * Common.position
and toplevel' =
  | TopDef of Common.variable * term
  | TopParam of Common.variable list * term
  | Context
  | Help
  | Quit

let rec string_of_term (term, loc) =
  begin
  match term with
  | Var x -> x
  | Type -> "Type"
  | Lambda(x,None,t2) ->
      "Lambda(" ^ x ^ "," ^ "_" ^ "," ^ (string_of_term t2) ^ ")"
  | Lambda(x,Some t1,t2) ->
      "Lambda(" ^ x ^ "," ^ (string_of_term t1) ^ "," ^ (string_of_term t2) ^ ")"
  | Pi(x,t1,t2) ->
      "Pi(" ^ x ^ "," ^ (string_of_term t1) ^ "," ^ (string_of_term t2) ^ ")"
  | Sigma(x,t1,t2) ->
      "Sigma(" ^ x ^ "," ^ (string_of_term t1) ^ "," ^ (string_of_term t2) ^ ")"
  | App(t1,t2) ->
      "App(" ^ (string_of_term t1) ^ "," ^ (string_of_term t2) ^ ")"
  | Pair(t1,t2) ->
      "Pair(" ^ (string_of_term t1) ^ "," ^ (string_of_term t2) ^ ")"
  | Proj(s1, t2) ->
      "Proj(\"" ^ s1 ^ "\"," ^ (string_of_term t2) ^ ")"
  | Ascribe(t1,t2) ->
      "Ascribe(" ^ (string_of_term t1) ^ "," ^ (string_of_term t2) ^ ")"
  | Operation(tag,terms) ->
      "Operation(" ^ (string_of_tag tag) ^ "," ^ (string_of_terms terms) ^ ")"
  | Handle(term, cases) ->
      "Handle(" ^ (string_of_term term) ^ "," ^ (String.concat "|" (List.map
      string_of_case cases)) ^ ")"
  end

and string_of_tag = function
  | Inhabit -> "Inhabit"
  | Equiv -> "Equiv"

and string_of_terms terms = (String.concat "," (List.map string_of_term terms))

and string_of_case (tag, terms, c) =
  (string_of_tag tag) ^ "(" ^ (string_of_terms terms) ^ ") => " ^ (string_of_term c)


let print term = print_endline (string_of_term term)

