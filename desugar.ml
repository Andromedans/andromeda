
module I = Input


(** Abstract syntax of terms as given by the user. *)
type term = term' * Common.position
and term' =
  | Var of int
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

and operation_tag = I.operation_tag =
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



(** Desugaring of input syntax to internal  *)

(** [index ~loc x xs] finds the location of [x] in the list [xs]. *)
let index ~loc x =
  let rec index k = function
    | [] -> Error.typing ~loc "unknown identifier %s" x
    | y :: ys -> if x = y then k else index (k + 1) ys
  in
    index 0

(** [doTerm xs e] converts an expression of type [I.expr] to type [expr] by
    replacing names in [e] with de Bruijn indices. Here [xs] is the list of names
    currently in scope (i.e., Context.names) *)
let rec doTerm xs (e, loc) =
  (match e with
    | I.Var x -> Var (index ~loc x xs)
    | I.Type  -> Type
    | I.Pi (x, t1, t2) -> Pi (x, doTerm xs t1, doTerm (x :: xs) t2)
    | I.Sigma (x, t1, t2) -> Sigma (x, doTerm xs t1, doTerm (x :: xs) t2)
    | I.Lambda (x, None  , e) -> Lambda (x, None, doTerm (x :: xs) e)
    | I.Lambda (x, Some t, e) -> Lambda (x, Some (doTerm xs t), doTerm (x :: xs) e)
    | I.App (e1, e2)   -> App (doTerm xs e1, doTerm xs e2)
    | I.Pair (e1, e2)   -> Pair (doTerm xs e1, doTerm xs e2)
    | I.Proj (s1, e2) -> Proj (s1, doTerm xs e2)
    | I.Ascribe (e, t) -> Ascribe (doTerm xs e, doTerm xs t)
    | I.Operation (optag, terms) -> Operation (optag, List.map (doTerm xs) terms)
    | I.Handle (term, h) -> Handle (doTerm xs term, handler xs h)
  ),
  loc

(*
and doComputation xs (c, loc) =
  (match c with
    | I.Return e -> Return (doTerm xs e)
    | I.Let (x, term1, c2) -> Let (x, doTerm xs term1, doComputation (x::xs) c2)),
  loc
  *)

and handler xs lst = List.map (handler_case xs) lst
(*
and handler_case xs (optag, terms, c) =
  (optag, List.map (doTerm xs) terms, doComputation xs c)
*)
and handler_case xs (optag, terms, c) =
  (optag, List.map (doTerm xs) terms, doTerm xs c)


  (* Based on similar shift code in Syntax *)

let rec shift ?(c=0) d (e, loc) =
  (match e with
  | Var m -> if (m < c) then Var m else Var(m+d)
  | Type  -> Type
  | Pi (x, t1, t2) -> Pi(x, shift ~c d t1, shift ~c:(c+1) d t2)
  | Sigma (x, t1, t2) -> Sigma(x, shift ~c d t1, shift ~c:(c+1) d t2)
  | Lambda (x, None, e) -> Lambda (x, None, shift ~c:(c+1) d e)
  | Lambda (x, Some t, e) -> Lambda (x, Some (shift ~c d t), shift ~c:(c+1) d e)
  | App (e1, e2) -> App(shift ~c d e1, shift ~c d e2)
  | Pair (e1, e2) -> Pair(shift ~c d e1, shift ~c d e2)
  | Proj (s1, e2) -> Proj(s1, shift ~c d e2)
  | Ascribe (e1, t2) -> Ascribe (shift ~c d e1, shift ~c d t2)
  | Operation (optag, terms) -> Operation (optag, List.map (shift ~c d) terms)
  | Handle (term, h) -> Handle (shift ~c d term, List.map (shift_handler_case ~c d) h)),
  loc

and shift_handler_case ?(c=0) d (optag, terms, term) =
  (* Correct only because we have no pattern matching ! *)
  (optag, List.map (shift ~c d) terms, shift ~c d term)


let rec string_of_term (term, loc) =
  begin
  match term with
  | Var i -> string_of_int i
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

and string_of_tag tag = I.string_of_tag tag

and string_of_terms terms = (String.concat "," (List.map string_of_term terms))

and string_of_case (tag, terms, c) =
  (string_of_tag tag) ^ "(" ^ (string_of_terms terms) ^ ") => " ^ (string_of_term c)


let print term = print_endline (string_of_term term)



