(** Abstract syntax of expressions and toplevel directives. *)

type universe = int

(** Abstract syntax of expressions. *)
type expr = expr' * Common.position
and expr' =
  | Var of int
  | Subst of substitution * expr (* explicit substitution *)
  | Universe of universe
  | Pi of abstraction
  | Lambda of abstraction
  | App of expr * expr

and substitution =
  | Shift of int
  | Dot of expr * substitution
 
(** An abstraction [(x,t,e)] indicates that [x] of (optionally given) type [t] is bound in [e]. *)
and abstraction = string * expr * expr

(** Constructors wrapped in "nowhere" positions. *)
let mk_var k = Common.nowhere (Var k)
let mk_subst s e = Common.nowhere (Subst (s, e))
let mk_universe u = Common.nowhere (Universe u)
let mk_pi a = Common.nowhere (Pi a)
let mk_arrow s t = mk_pi ("_", s, t)
let mk_lambda a = Common.nowhere (Lambda a)
let mk_app e1 e2 = Common.nowhere (App (e1, e2))

let lookup_var k ctx = snd (List.nth ctx k)

let extend_var x e sbst = (x, e) :: sbst

let idsubst = Shift 0

let rec compose s t =
  match s, t with
    | t, Shift 0 -> t
    | Dot (e, t), Shift m -> compose t (Shift (m - 1))
    | Shift m, Shift n -> Shift (m + n)
    | t, Dot (e, s) -> Dot (mk_subst t e, compose t s)

(** [reduce e] substitutes away all explicit substitions in expression [e]. *)
let rec reduce s ((e', loc) as e) =
  match s, e' with
    | Shift m, Var k -> Var (k + m), loc
    | Dot (a, s), Var 0 -> reduce idsubst a
    | Dot (a, s), Var k -> reduce s (Var (k - 1), loc)
      | s, Subst (t, e) -> reduce s (reduce t e)
      | _, Universe _ -> e
      | s, Pi a -> Pi (reduce_abstraction s a), loc
      | s, Lambda a -> Lambda (reduce_abstraction s a), loc
      | s, App (e1, e2) -> App (reduce s e1, reduce s e2), loc

and reduce_abstraction s (x, e1, e2) =
  (x, reduce s e1, reduce (Dot (mk_var 0, compose (Shift 1) s)) e2)

let shift k e = reduce (Shift k) e

let rec occurs k (e, _) =
  match e with
    | Var m -> m = k
    | Subst (Shift m, e) -> k >= m && occurs (k - m) e
    | Subst (Dot (e1, s), e2) -> (occurs 0 e2 && occurs k e1) || occurs (k - 1) (mk_subst s e2)
    | Universe _ -> false
    | Pi a -> occurs_abstraction k a
    | Lambda a -> occurs_abstraction k a
    | App (e1, e2) -> occurs k e1 || occurs k e2

and occurs_abstraction k (_, e1, e2) =
  occurs k e1 || occurs (k + 1) e2

  
