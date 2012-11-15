(** Abstract syntax of expressions and toplevel directives. *)

type variable = Common.variable

(** Abstract syntax of expressions. *)
type expr = expr' * Common.position
and expr' =
  | Var of variable
  | EVar of int * expr
  | Universe of Universe.universe
  | Pi of abstraction
  | Lambda of abstraction
  | App of expr * expr
  | Ascribe of expr * expr
 
(** An abstraction [(x,t,e)] indicates that [x] of (optionally given) type [t] is bound in [e]. *)
and abstraction = variable * expr * expr

(** Toplevel directives. *)
type directive = directive' * Common.position
and directive' =
  | Quit
  | Help
  | Context
  | Parameter of variable * expr
  | Definition of variable * expr
  | Check of expr
  | Eval of expr

(** Constructors wrapped in "nowhere" positions. *)
let mk_var v = Common.nowhere (Var v)
let mk_evar (v,k) = Common.nowhere (EVar (v,k))
let mk_universe u = Common.nowhere (Universe u)
let mk_pi a = Common.nowhere (Pi a)
let mk_lambda a = Common.nowhere (Lambda a)
let mk_app e1 e2 = Common.nowhere (App (e1, e2))
let mk_ascribe e1 e2 = Common.nowhere (Ascribe (e1, e2))

(** A substitution is a mapping that maps:
    - variables to expressions (without positions)
    - existential variables to expressions (without positions)
    - existential universe variables to universes
*)
type substitution = {
  vars : (variable * expr') list ;
  evars : (int * expr') list ;
  uvars : (Universe.uvar * Universe.universe) list
}

let empty_subst = {
  vars = [];
  evars = [];
  uvars = []
}

let lookup_var x {vars = vs} = List.assoc x vs

let lookup_evar x {evars = es} = List.assoc x es

let lookup_uvar x {uvars = us} = List.assoc x us

let extend_var x e s = {s with vars = (x,e) :: s.vars}

let extend_evar x e s = {s with evars = (x,e) :: s.evars}

let extend_uvar x e s = {s with uvars = (x,e) :: s.uvars}

(** Generate a fresh existential variable of a given type [t] *)
let fresh_evar = 
  let k = ref 0 in
    fun t -> (incr k ; mk_evar (!k, t))

let fresh_tvar () = fresh_evar (mk_universe (Universe.fresh_universe ()))

(** [subst s e] performs the given substitution [s] in expression [e]. *)
let rec subst s (e, loc) = 
  Common.nowhere
    (match e with
      | Var x -> (try lookup_var x s with Not_found -> e)
      | EVar (k, _) -> (try lookup_evar k s with Not_found -> e)
      | Universe u -> Universe (Universe.subst_universe s.uvars u)
      | Pi a -> Pi (subst_abstraction s a)
      | Lambda a -> Lambda (subst_abstraction s a)
      | App (e1, e2) -> App (subst s e1, subst s e2)
      | Ascribe (e1, e2) -> Ascribe (subst s e1, subst s e2)
    )

and subst_abstraction s (x, t, e) =
  let x' = Common.refresh x in
    (x', subst s t, subst (extend_var x (Var x') s) e)
