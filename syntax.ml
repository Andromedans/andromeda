(** Abstract syntax of expressions and toplevel directives. *)

type variable = Common.variable

(** Abstract syntax of expressions. *)
type expr = expr' * Common.position
and expr' =
  | Var of variable
  | EVar of meta_variable
  | Universe of Universe.universe
  | Pi of abstraction
  | Lambda of abstraction
  | App of expr * expr
  | Ascribe of expr * expr
 
(** An abstraction [(x,t,e)] indicates that [x] of (optionally given) type [t] is bound in [e]. *)
and abstraction = variable * expr * expr

(** Meta-variables are for internal purposes only, therefore we may as well index them by
    integers. Every meta-variable carries its type and a context in which it lives. This
    is necessary because a meta-variable must be instantiated to a term which lives in the
    context of the meta-variable, but we might instantiate later on when the context is
    not available anymore.
*)
and meta_variable = int * context * expr

(** A context is represented as an associative list which maps a variable [x] to a pair
   [(t,e)] where [t] is its type and [e] is its value (optional).
*)
and context = (variable * (expr' * expr option)) list

(** Handling of contexts. *)
    
(** [lookup_ty x ctx] returns the type of [x] in context [ctx]. *)
let lookup_ty x ctx = fst (List.assoc x ctx)

(** [lookup_ty x ctx] returns the value of [x] in context [ctx], or [None] 
    if [x] has no assigned value. *)
let lookup_value x ctx = snd (List.assoc x ctx)

(** [extend x t ctx] returns [ctx] extended with variable [x] of type [t],
    whereas [extend x t ~value:e ctx] returns [ctx] extended with variable [x]
    of type [t] and assigned value [e]. *)
let extend x t ?value ctx = (x, (t, value)) :: ctx

(** Constructors wrapped in "nowhere" positions. *)
let mk_var v = Common.nowhere (Var v)
let mk_evar x = Common.nowhere (EVar x)
let mk_universe u = Common.nowhere (Universe u)
let mk_pi a = Common.nowhere (Pi a)
let mk_arrow s t = mk_pi (Common.Anonymous, s, t)
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
let fresh_evar' = 
  let k = ref 0 in
    fun ctx t -> (incr k ; EVar (!k, ctx, t))

let fresh_evar ctx t = Common.nowhere (fresh_evar' ctx t)

let fresh_tvar' () = fresh_evar' [] (mk_universe (Universe.fresh ()))

(** [subst s e] performs the given substitution [s] in expression [e]. *)
let rec subst s (e, loc) = 
  (match e with
    | Var x -> (try lookup_var x s with Not_found -> e)
    | EVar (k, _, _) -> (try lookup_evar k s with Not_found -> e)
    | Universe u -> Universe (Universe.subst s.uvars u)
    | Pi a -> Pi (subst_abstraction s a)
    | Lambda a -> Lambda (subst_abstraction s a)
    | App (e1, e2) -> App (subst s e1, subst s e2)
    | Ascribe (e1, e2) -> Ascribe (subst s e1, subst s e2)),
  loc

and subst_abstraction s (x, t, e) =
  let x' = Common.refresh x in
    (x', subst s t, subst (extend_var x (Var x') s) e)
