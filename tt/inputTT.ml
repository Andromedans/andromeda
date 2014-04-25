(** Abstract syntax of parsed input. *)

type universe = Universe.t
  | NonFib of int
  | Fib of int

type eqsort =
  | Ju
  | Pr

type operation_tag = string

type tt_var = Common.name

type const =
  | Int of int
  | Bool of bool
  | Unit

type primop =
  | Plus
  | Not
  | And
  | Append

type 'a exp = 'a exp' * Common.position
and 'a exp' =
  | Var of tt_var
  | Fun of tt_var * 'a computation
  | Handler of handler
  | ContExp of Brazil.ty list * Brazil.ty list * 'a cont
  | Term   of Brazil.term
  | Type   of Brazil.type
  | Tuple  of 'a exp list
  | Const  of const
  | Inj    of int * 'a exp

and 'a computation =
  | Val of 'a exp
  | App of 'a exp * 'a exp
  | Let of tt_var * 'a computation * 'a computation
  | Op  of operation_tag * exp list
  | WithHandle of 'a exp * 'a computation
  | KApp of 'a exp * 'a exp
  | Ascribe of 'a exp * 'a exp
  | Prim of primop * 'a exp list
  | Match of 'a exp * 'a arm list
  | MkVar of int
  | MkLam of Common.name * 'a exp * 'a computation
  | MkApp of 'a exp * 'a exp

and 'a cont =
  | KHole
  | KLet of tt-var * 'a cont * 'a computation
  | KWithHAndle of 'a exp * 'a cont
  | KMkLam of Common.name * Brazil.ty * 'a cont

and 'a arm = pattern * 'a computation

and 'a handler =
  { valH : (tt_var * 'a cont);
    opH  : operation_tag * (tt_var list * tt_var * 'a computation) list;
  }

and pattern =
  | PTuple of tt_var list
  | PInj of int * tt_var
  | PConst of const

and result =
  | RVal of Common.debruijn exp
  | ROp of operation-tag * (tt_var list * Common.debruijn exp * Common.debruijn cont)

type 'a toplevel = 'a toplevel' * Common.position
and 'a toplevel' =
  | TopDef of Common.variable * 'a term option * 'a term
  | TopParam of Common.variable list * 'a term
  | TopHandler of 'a handler
  | Context
  | Help
  | Quit

(** String conversion functions to be used only for debugging where proper printing of
    terms is not available. *)

let embrace s = "(" ^ s ^ ")"
let app_embrace h lst = h ^ embrace (String.concat ", " lst)

let string_of_tag otag = otag

let string_of_universe = Universe.string_of_universe

let string_of_term string_of_var =
  let rec to_str (term, loc) =
  begin
    match term with
    | Var x -> "Var[" ^ string_of_var x ^ "]"
    | Universe u -> string_of_universe u
    | Lambda(x,None,t2) -> app_embrace "Lambda" [x; "-"; to_str t2]
    | Lambda(x,Some t1,t2) -> app_embrace "Lambda" [x; to_str t1; to_str t2]
    | Pi(x,None,t2) -> app_embrace "Pi" [x; "-"; to_str t2]
    | Pi(x,Some t1,t2) -> app_embrace "Pi" [x; to_str t1; to_str t2]
    | Sigma(x,None,t2) -> app_embrace "Sigma" [x; "-"; to_str t2]
    | Sigma(x,Some t1,t2) -> app_embrace "Sigma" [x; to_str t1; to_str t2]
    | App(t1,t2) -> app_embrace "App" [to_str t1; to_str t2]
    | Pair(t1,t2) -> app_embrace "Pair" [to_str t1; to_str t2]
    | Proj(s1, t2) -> app_embrace "Proj" [s1; to_str t2]
    | Ascribe(t1,t2) -> app_embrace "Ascribe" [to_str t1; to_str t2]
    | Operation(tag,terms) -> app_embrace "Operation" (string_of_tag tag :: List.map to_str terms)
    | Handle(term, cases) ->
      app_embrace "Handle" [to_str term; (String.concat "|" (List.map string_of_case cases))]
    | Equiv(o,t1,t2,t3) -> app_embrace "Equiv" [string_of_eqsort o; to_str t1; to_str t2; to_str t3]
    | Refl(o,t) -> app_embrace "Refl" [string_of_eqsort o; to_str t]
    | Ind((x,y,p,c),(z,w),q) ->
      app_embrace "Ind" [embrace (String.concat " . " [x; y; p; to_str c]) ;
                         embrace (z ^ " . " ^ to_str w) ;
                         to_str q]
    | Wildcard -> "?"
    | Admit -> "ADMIT"
   end

  and string_of_case (tag, terms, c) =
    app_embrace (string_of_tag tag) (List.map to_str terms) ^ " => " ^ to_str c
  in
    to_str

let printI term = print_endline (string_of_term (fun s -> s) term)

(********************************************)
(** Desugaring of input syntax to internal  *)
(********************************************)

(** [index ~loc x xs] finds the location of [x] in the list [xs]. *)
let index ~loc x =
  let rec index k = function
    | [] -> Error.typing ~loc "unknown identifier %s" x
    | y :: ys -> if x = y then k else index (k + 1) ys
  in
    index 0

(** [desugar xs e] converts an expression of type [Common.variable expr] to type
    [Common.debruijn expr] by
    replacing names in [e] with de Bruijn indices. Here [xs] is the list of names
    currently in scope (e., Context.names) *)
let rec desugar xs (e, loc) =
  (match e with
    | Var x -> Var (index ~loc x xs)
    | Universe u  -> Universe u
    | Pi (x, t_opt, e) -> Pi (x, desugar_opt xs t_opt, desugar (x :: xs) e)
    | Sigma (x, t_opt, e) -> Sigma (x, desugar_opt xs t_opt, desugar (x :: xs) e)
    | Lambda (x, t_opt, e) -> Lambda (x, desugar_opt xs t_opt, desugar (x :: xs) e)
    | App (e1, e2)   -> App (desugar xs e1, desugar xs e2)
    | Pair (e1, e2)   -> Pair (desugar xs e1, desugar xs e2)
    | Proj (s1, e2) -> Proj (s1, desugar xs e2)
    | Ascribe (e, t) -> Ascribe (desugar xs e, desugar xs t)
    | Operation (optag, terms) -> Operation (optag, List.map (desugar xs) terms)
    | Handle (term, h) -> Handle (desugar xs term, desugar_handler xs h)
    | Equiv (o, t1, t2, t3) -> Equiv (o, desugar xs t1, desugar xs t2, desugar xs t3)
    | Refl (o, t) -> Refl(o, desugar xs t)
    | Ind ((x,y,p,c), (z, w), q) ->
         Ind((x,y,p, desugar (p::y::x::xs) c),
                   (z, desugar (z::xs) w),
                   desugar xs q)
    | Wildcard -> Wildcard
    | Admit -> Admit
  ),
  loc

and desugar_handler xs lst = List.map (desugar_case xs) lst

and desugar_case xs (optag, terms, c) =
  (optag, List.map (desugar xs) terms, desugar xs c)

and desugar_opt xs = function
  | None   -> None
  | Some e -> Some (desugar xs e)


  (* Based on similar shift code in Syntax *)

let rec shift ?(cut=0) delta (e, loc) =
  (match e with
  | Var m -> if (m < cut) then Var m else Var(m+delta)
  | Universe u  -> Universe u
  | Wildcard -> Wildcard
  | Admit -> Admit
  | Pi (x, t_opt, e) -> Pi (x, shift_opt ~cut delta t_opt, shift ~cut:(cut+1) delta e)
  | Sigma (x, t_opt, e) -> Sigma (x, shift_opt ~cut delta t_opt, shift ~cut:(cut+1) delta e)
  | Lambda (x, t_opt, e) -> Lambda (x, shift_opt ~cut delta t_opt, shift ~cut:(cut+1) delta e)
  | App (e1, e2) -> App(shift ~cut delta e1, shift ~cut delta e2)
  | Pair (e1, e2) -> Pair(shift ~cut delta e1, shift ~cut delta e2)
  | Proj (s1, e2) -> Proj(s1, shift ~cut delta e2)
  | Ascribe (e1, t2) -> Ascribe (shift ~cut delta e1, shift ~cut delta t2)
  | Operation (optag, terms) -> Operation (optag, List.map (shift ~cut delta) terms)
  | Handle (term, h) -> Handle (shift ~cut delta term, List.map (shift_handler_case ~cut delta) h)
  | Equiv (o, t1, t2, t3) -> Equiv (o, shift ~cut delta t1, shift ~cut delta t2, shift ~cut delta t3)
  | Refl (o, t) -> Refl (o, shift ~cut delta t)
  | Ind ((x,y,p,c), (z,w), q) ->
        Ind ((x,y,p,shift ~cut:(cut+3) delta c),
                  (z, shift ~cut:(cut+1) delta w),
                  (shift ~cut delta q))),
  loc

and shift_handler_case ?(cut=0) delta (optag, terms, term) =
  (* Correct only because we have no pattern matching ! *)
  (optag, List.map (shift ~cut delta) terms, shift ~cut delta term)

and shift_opt ?(cut=0) delta = function
  | None -> None
  | Some e -> Some (shift ~cut delta e)

(** [shift_to_depth (k,exp) l] moves the expression [exp] from a context
      with depth [k] to a context of depth [l >= k].

      Equivalently, weaken with [l - k] new variables at the end of the
      context. *)
let shift_to_depth (old_depth, exp) new_depth =
  assert (new_depth >= old_depth);
  shift (new_depth - old_depth) exp

let print =
  let to_string = string_of_term string_of_int  in
  function term -> print_endline (to_string term)



