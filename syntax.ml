(** Abstract syntax of internal expressions. *)

(** Universes are indexed by natural numbers. *)
type universe = int

(** Abstract syntax of expressions, where de Bruijn indices are used to represent
    variables. *)
type expr = expr' * Common.position
and expr' =
  | Var of int                   (* de Briujn index *)
  | Subst of substitution * expr (* explicit substitution *)
  | Universe of universe
  | Pi of Common.variable * expr * expr
  | Lambda of Common.variable * expr
  | App of expr * expr
  | Ascribe of expr * expr

(** An abstraction [(x,t,e)] indicates that [x] of type [t] is bound in [e]. We also keep around
    the original name [x] of the bound variable for pretty-printing purposes. *)
and abstraction = Common.variable * expr * expr

(** Explicit substitutions. *)
and substitution =
  | Shift of int
  | Dot of expr * substitution
 
(** Expression constructors wrapped in "nowhere" positions. *)
let mk_var k = Common.nowhere (Var k)
let mk_subst s e = Common.nowhere (Subst (s, e))
let mk_universe u = Common.nowhere (Universe u)
let mk_pi x t e = Common.nowhere (Pi (x, t, e))
let mk_arrow s t = mk_pi "_" s t
let mk_lambda x e = Common.nowhere (Lambda (x, e))
let mk_app e1 e2 = Common.nowhere (App (e1, e2))
let mk_ascribe e t = Common.nowhere (Ascribe (e, t))

(** The identity substiution. *)
let idsubst = Shift 0

(** [shift k e] shifts the indices in [e] by [k] places. *)
let shift k e = mk_subst (Shift k) e

(** [compose s t] composes explicit subtitutions [s] and [t], i.e.,
    we have [subst (compose s t) e = subst s (subst t e)]. *)
let rec compose s t =
  match s, t with
    | s, Shift 0 -> s
    | Dot (e, s), Shift m -> compose s (Shift (m - 1))
    | Shift m, Shift n -> Shift (m + n)
    | s, Dot (e, t) -> Dot (mk_subst s e, compose s t)

(** [subst s e] applies explicit substitution [s] in expression [e]. It does so
    lazily, i.e., it does just enough to expose the outermost constructor of [e]. *)
let subst =
  let rec subst s ((e', loc) as e) =
    match s, e' with
      | Shift m, Var k -> Var (k + m), loc
      | Dot (a, s), Var 0 -> subst idsubst a
      | Dot (a, s), Var k -> subst s (Var (k - 1), loc)
      | s, Subst (t, e) -> subst s (subst t e)
      | _, Universe _ -> e
      | s, Pi (x, t1, t2) ->
        let t1 = mk_subst s t1 in
        let t2 = mk_subst (Dot (mk_var 0, compose (Shift 1) s)) t2 in
          Pi (x, t1, t2), loc
      | s, Lambda (x, e) ->
        let e = mk_subst (Dot (mk_var 0, compose (Shift 1) s)) e in
          Lambda (x, e), loc
      | s, App (e1, e2) -> App (mk_subst s e1, mk_subst s e2), loc
      | s, Ascribe (e, t) -> Ascribe (mk_subst s e, mk_subst s t), loc
  in
    subst

(** [occurs k e] returns [true] when variable [Var k] occurs freely in [e]. *)
let rec occurs k (e, _) =
  match e with
    | Var m -> m = k
    | Subst (s, e) -> occurs k (subst s e)
    | Universe _ -> false
    | Pi (_, t1, t2) -> occurs k t1 || occurs (k + 1) t2
    | Lambda (_, e) -> occurs (k + 1) e
    | App (e1, e2) -> occurs k e1 || occurs k e2
    | Ascribe (e, t) -> occurs k e || occurs k t
