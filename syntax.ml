type variable =
  | String of string
  | Gensym of string * int
  | Dummy

type universe = int

type expr =
  | Var of variable
  | Universe of universe
  | Pi of abstraction
  | Lambda of abstraction
  | App of expr * expr

and abstraction = variable * expr * expr

type directive =
  | Quit
  | Help
  | Context
  | Parameter of variable * expr
  | Definition of variable * expr
  | Check of expr
  | Eval of expr

let refresh =
  let k = ref 0 in
    function
      | String x | Gensym (x, _) -> (incr k ; Gensym (x, !k))
      | Dummy -> (incr k ; Gensym ("_", !k))

let rec subst s = function
  | Var x -> (try List.assoc x s with Not_found -> Var x)
  | Universe k -> Universe k
  | Pi a -> Pi (subst_abstraction s a)
  | Lambda a -> Lambda (subst_abstraction s a)
  | App (e1, e2) -> App (subst s e1, subst s e2)

and subst_abstraction s (x, t, e) =
  let x' = refresh x in
    (x', subst s t, subst ((x, Var x') :: s) e)
