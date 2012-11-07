
(** During substitution we generate fresh variable names. Because we want pretty printing,
    each freshly generated variable name should "remember" its preferred form. Thus a
    variable name has three possible form. It can be a string, as originally given by
    the user, or it can be a generated fresh name consisting of preferred name and a counter,
    or it can be a dummy, indicating that it is never used.
*)
type variable =
  | String of string
  | Gensym of string * int
  | Dummy

(** Universes are indexed by numerals. *)
type universe = int

(** Abstract syntax of expressions. *)
type expr =
  | Var of variable
  | Universe of universe
  | Pi of abstraction
  | Lambda of abstraction
  | App of expr * expr

and abstraction = variable * expr * expr

(** Toplevel directives. *)
type directive =
  | Quit
  | Help
  | Context
  | Parameter of variable * expr
  | Definition of variable * expr
  | Check of expr
  | Eval of expr

(** [refresh x] generates a fresh variable name whose preferred form is [x]. *)
let refresh =
  let k = ref 0 in
    function
      | String x | Gensym (x, _) -> (incr k ; Gensym (x, !k))
      | Dummy -> (incr k ; Gensym ("_", !k))

(** [subst [(x1,e1); ...; (xn;en)] e] performs the given substitution of
    expressions [e1], ..., [en] for variables [x1], ..., [xn] in expression [e]. *)
let rec subst s = function
  | Var x -> (try List.assoc x s with Not_found -> Var x)
  | Universe k -> Universe k
  | Pi a -> Pi (subst_abstraction s a)
  | Lambda a -> Lambda (subst_abstraction s a)
  | App (e1, e2) -> App (subst s e1, subst s e2)

and subst_abstraction s (x, t, e) =
  let x' = refresh x in
    (x', subst s t, subst ((x, Var x') :: s) e)
