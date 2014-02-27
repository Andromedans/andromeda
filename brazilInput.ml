(** Absng_tract syntax of input files. *)

(** Abstract syntax of terms as given by the user. *)
type 'a term = 'a term' * Common.position
and 'a term' =
  | Var of 'a
  | Num of int
  | Universe of universe
  | Lambda of Common.variable * 'a term option * 'a term
  | Pi of Common.variable * 'a term * 'a term
  | App of 'a term * 'a term
  | Sigma of Common.variable * 'a term * 'a term
  | Pair of 'a term * 'a term
  | Proj of string * 'a term
  | Ascribe of 'a term * 'a term      (* Technically unnecessary for Brazil *)
  | Handle of 'a term * 'a handler list
  | Equiv of eqsort * 'a term * 'a term * 'a term
  | J of eqsort * 'a term * 'a term * 'a term
  | Refl of eqsort * 'a term


and universe = Input.universe =
  | Type of int
  | Fib of int

and eqsort = Input.eqsort =
  | Ju
  | Pr

and 'a handler = 'a term

type 'a toplevel = 'a toplevel' * Common.position
and 'a toplevel' =
  | TopDef of Common.variable * 'a term
  | TopParam of Common.variable list * 'a term
  | TopHandler of 'a handler list
  | Context
  | Help
  | Quit

(*********************************************)
(* Raw string representations, for debugging *)
(*********************************************)

let string_of_universe = function
  | Type i -> "Type(" ^ string_of_int i ^ ")"
  | Fib  i -> "Fib(" ^ string_of_int i ^ ")"

let string_of_eqsort = function
  | Ju -> "Ju"
  | Pr -> "Pr"

let rec string_of_term string_of_var =
  let rec loop = function (term, loc) ->
    match term with
    | Var x -> string_of_var x
    | Num n -> string_of_int n
    | Universe u -> string_of_universe u
    | Lambda(x,None,t2) ->
      "Lambda(" ^ x ^ "," ^ "_" ^ "," ^ (loop t2) ^ ")"
    | Lambda(x,Some t1,t2) ->
        "Lambda(" ^ x ^ "," ^ (loops [t1;t2]) ^ ")"
    | Pi(x,t1,t2) ->
        "Pi(" ^ x ^ "," ^ (loops [t1;t2]) ^ ")"
    | Sigma(x,t1,t2) ->
        "Sigma(" ^ x ^ "," ^ (loops [t1;t2]) ^ ")"
    | App(t1,t2) ->
        "App(" ^ (loops [t1;t2]) ^ ")"
    | Pair(t1,t2) ->
        "Pair(" ^ (loops [t1;t2]) ^ ")"
    | Proj(s1, t2) ->
        "Proj(\"" ^ s1 ^ "\"," ^ (loop t2) ^ ")"
    | Ascribe(t1,t2) ->
        "Ascribe(" ^ (loops [t1;t2]) ^ ")"
    | Handle(term, cases) ->
        "Handle(" ^ (loop term) ^ "," ^
      loops cases ^ ")"
    | Equiv(o,t1,t2,t3) ->
        "Equiv(" ^ (string_of_eqsort o) ^ "," ^ loops [t1; t2; t3] ^ ")"
    | J(o,t1,t2,t3) ->
        "J(" ^ (string_of_eqsort o) ^ "," ^ loops [t1; t2; t3] ^ ")"
    | Refl(o,t) ->
        "Refl(" ^ (string_of_eqsort o) ^ "," ^ loop t ^ ")"

     and loops terms =
        (String.concat "," (List.map loop terms))

  in loop

let printI term = print_endline (string_of_term (fun s -> s) term)


(********************************************)
(** desugaring of input syntax to internal  *)
(********************************************)

(** [index ~loc x xs] finds the location of [x] in the list [xs]. *)
let index ~loc x =
  let rec index k = function
    | [] -> Error.typing ~loc "unknown identifier %s" x
    | y :: ys -> if x = y then k else index (k + 1) ys
  in
    index 0

(** [desugar xs e] converts an expression of type [expr] to type [expr] by
    replacing names in [e] with de Bruijn indices. Here [xs] is the list of names
    currently in scope (e., Context.names) *)
let rec desugar xs (e, loc) =
  (match e with
    | Var x -> Var (index ~loc x xs)
    | Num n -> Num n
    | Universe u -> Universe u
    | Pi (x, t1, t2) -> Pi (x, desugar xs t1, desugar (x :: xs) t2)
    | Sigma (x, t1, t2) -> Sigma (x, desugar xs t1, desugar (x :: xs) t2)
    | Lambda (x, None  , e) -> Lambda (x, None, desugar (x :: xs) e)
    | Lambda (x, Some t, e) -> Lambda (x, Some (desugar xs t), desugar (x :: xs) e)
    | App (e1, e2)   -> App (desugar xs e1, desugar xs e2)
    | Pair (e1, e2)   -> Pair (desugar xs e1, desugar xs e2)
    | Proj (s1, e2) -> Proj (s1, desugar xs e2)
    | Ascribe (e, t) -> Ascribe (desugar xs e, desugar xs t)
    | Handle (term, h) -> Handle (desugar xs term, desugar_handler xs h)
    | Equiv (o, t1, t2, t3) -> Equiv (o, desugar xs t1, desugar xs t2, desugar xs t3)
    | J (o, t1, t2, t3) -> J (o, desugar xs t1, desugar xs t2, desugar xs t3)
    | Refl (o, t) -> Refl(o, desugar xs t)
  ),
  loc

and desugar_handler xs lst = List.map (desugar xs) lst

  (* Based on similar shift code in Syntax *)

let rec shift ?(c=0) d (e, loc) =
  (match e with
  | Var m -> if (m < c) then Var m else Var(m+d)
  | Num n -> Num n
  | Universe u -> Universe u
  | Pi (x, t1, t2) -> Pi(x, shift ~c d t1, shift ~c:(c+1) d t2)
  | Sigma (x, t1, t2) -> Sigma(x, shift ~c d t1, shift ~c:(c+1) d t2)
  | Lambda (x, None, e) -> Lambda (x, None, shift ~c:(c+1) d e)
  | Lambda (x, Some t, e) -> Lambda (x, Some (shift ~c d t), shift ~c:(c+1) d e)
  | App (e1, e2) -> App(shift ~c d e1, shift ~c d e2)
  | Pair (e1, e2) -> Pair(shift ~c d e1, shift ~c d e2)
  | Proj (s1, e2) -> Proj(s1, shift ~c d e2)
  | Ascribe (e1, t2) -> Ascribe (shift ~c d e1, shift ~c d t2)
  | Handle (term, h) -> Handle (shift ~c d term, List.map (shift ~c d) h)
  | Equiv (o, t1, t2, t3) -> Equiv (o, shift ~c d t1, shift ~c d t2, shift ~c d t3)
  | J (o, t1, t2, t3) -> J (o, shift ~c d t1, shift ~c d t2, shift ~c d t3)
  | Refl (o, t) -> Refl (o, shift ~c d t)),
  loc

let print term = print_endline (string_of_term string_of_int term)



