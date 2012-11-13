(** Abstract syntax of expressions and toplevel directives. *)

type variable = Common.variable

(** Abstract syntax of expressions. *)
type expr = expr' * Common.position
and expr' =
  | Var of variable
  | EVar of int
  | Universe of int
  | Pi of abstraction
  | Lambda of abstraction
  | App of expr * expr
 
(** An abstraction [(x,t,e)] indicates that [x] of (optionally given) type [t] is bound in [e]. *)
and abstraction = variable * expr * expr

(** [subst [(x1,e1); ...; (xn;en)] e] performs the given substitution of
    expressions [e1], ..., [en] for variables [x1], ..., [xn] in expression [e]. *)
let rec subst s (e, loc) = 
  Common.nowhere
    (match e with
      | Var x -> (try List.assoc x s with Not_found -> Var x)
      | Universe k -> Universe k
      | Pi a -> Pi (subst_abstraction s a)
      | Lambda a -> Lambda (subst_abstraction s a)
      | App (e1, e2) -> App (subst s e1, subst s e2))

and subst_abstraction s (x, t, e) =
  let x' = Common.refresh x in
    (x', subst s t, subst ((x, Var x') :: s) e)
