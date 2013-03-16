(** Abstract syntax of internal expressions. *)

(** Abstract syntax of expressions, where de Bruijn indices are used to represent
    variables. *)
type term = term' * Common.position
and term' =
  | Var of int
  | Subst of substitution * term
  | Pi of Common.variable * sort * sort
  | Lambda of Common.variable * sort option * term
  | App of term * term
  | Ascribe of term * sort
  | Type
  | Kind
  | TyWtn
  | EqWtn
  | TyJdg of term * sort
  | EqJdg of term * term * sort

and sort = term

(** Explicit substitutions. *)
and substitution =
  | Shift of int
  | Dot of term * substitution

type operation =
  | Inhabit of sort                   (* inhabit a sort *)
  | Infer of term                     (* infer the sort of expression *)
  | HasType of term * sort            (* inhabit a typing judgment *)
  | Equal of term * term * sort       (* inhabit judgmental equality *)

(** Computations. *)
type computation =
  | Let of Common.variable * computation * computation
  | Param of Common.variable * sort * computation
  | Operation of operation

(** Expression constructors wrapped in "nowhere" positions. *)
let mk_var k = Common.nowhere (Var k)
let mk_subst s e = Common.nowhere (Subst (s, e))
let mk_pi x t1 t2 = Common.nowhere (Pi (x, t1, t2))
let mk_lambda x t e = Common.nowhere (Lambda (x, t, e))
let mk_app e1 e2 = Common.nowhere (App (e1, e2))
let mk_ascribe e t = Common.nowhere (Ascribe (e, t))
let mk_type = Common.nowhere Type
let mk_kind = Common.nowhere Kind
let mk_eqwtn = Common.nowhere EqWtn
let mk_eqjdg e1 e2 t = Common.nowhere (EqJdg (e1, e2, t))
let mk_tywtn = Common.nowhere TyWtn
let mk_tyjdg e t = Common.nowhere (TyJdg (e, t))

(** The identity substitution. *)
let idsubst = Shift 0

(** [shift k e] shifts the indices in [e] by [k] places. *)
let shift k e = mk_subst (Shift k) e

(** [compose s t] composes explicit subtitutions [s] and [t], i.e.,
    we have [subst (compose s t) e = subst s (subst t e)]. *)
let rec compose s t =
  match s, t with
    | s, Shift 0 -> s
    | Dot (_, s), Shift m -> compose s (Shift (m - 1))
    | Shift m, Shift n -> Shift (m + n)
    | s, Dot (e, s') -> Dot (mk_subst s e, compose s s')

(** [subst s e] applies explicit substitution [s] in expression [e]. It does so
    lazily, i.e., it does just enough to expose the outermost constructor of [e]. *)
let subst =
  let rec subst s (e', loc) =
    match s, e' with
      | Shift m, Var k -> Var (k + m), loc
      | Dot (a, s), Var 0 -> a
      | Dot (a, s), Var k -> subst s (Var (k - 1), loc)
      | s, Subst (t, e) -> subst s (subst t e)
      | s, Pi (x, t1, t2) ->
        let t1 = mk_subst s t1 in
        let t2 = mk_subst (Dot (mk_var 0, compose (Shift 1) s)) t2 in
          Pi (x, t1, t2), loc
      | s, Lambda (x, t, e) ->
        let t = (match t with None -> None | Some t -> Some (mk_subst s t)) in
        let e = mk_subst (Dot (mk_var 0, compose (Shift 1) s)) e in
          Lambda (x, t, e), loc
      | s, App (e1, e2) -> App (mk_subst s e1, mk_subst s e2), loc
      | s, Ascribe (e, t) -> Ascribe (mk_subst s e, mk_subst s t), loc
      | s, (Type|Kind|TyWtn|EqWtn) -> e', loc
      | s, TyJdg (e, t) ->
        let e = mk_subst s e in
        let t = mk_subst s t in
          TyJdg (e, t), loc
      | s, EqJdg (e1, e2, t) ->
        let e1 = mk_subst s e1 in
        let e2 = mk_subst s e2 in
        let t = mk_subst s t in
          EqJdg (e1, e2, t), loc
  in
    subst

(** [occurs k e] returns [true] when variable [Var k] occurs freely in [e]. *)
let rec occurs k (e, _) =
  match e with
    | Var m -> m = k
    | Subst (s, e) -> occurs k (subst s e)
    | Pi (_, t1, t2) -> occurs k t1 || occurs (k + 1) t2
    | Lambda (_, None, e) -> occurs (k + 1) e
    | Lambda (_, Some t, e) -> occurs k t || occurs (k + 1) e
    | App (e1, e2) -> occurs k e1 || occurs k e2
    | Ascribe (e, t) -> occurs k e || occurs k t
    | Type | Kind | TyWtn | EqWtn -> false
    | EqJdg (e1, e2, t) -> occurs k t || occurs k e1 || occurs k e2
    | TyJdg (e, t) -> occurs k t || occurs k e
