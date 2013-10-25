(** Abstract syntax of internal expressions. *)

module D = Desugar

(** Abstract syntax of expressions, where de Bruijn indices are used to represent
    variables. *)
type expr =
  | Var of int
  | Lambda of Common.variable * ty * expr
  | App of expr * expr

and ty =
  | TVar of int
  | TPi of Common.variable * ty * ty
  | TApp of ty * expr

and kind =
  | KType
  | KPi of Common.variable * ty * kind

  (*
(** Explicit substitutions. *)
and substitution =
  | Shift of int
  | Dot of expr * substitution
  *)

  (** [shift c d] shifts the indices by [d] with a cutoff of [c]. *)
  (* See, e.g., http://ecee.colorado.edu/~siek/ecen5013/spring10/lecture4.pdf *)

let rec shift ?(c=0) d = function
  | Var m -> if (m < c) then Var m else Var(m+d)
  | Lambda (x, t, e) -> Lambda (x, shiftTy ~c:c d t, shift ~c:(c+1) d e)
  | App (e1, e2) -> App(shift ~c:c d e1, shift ~c:c d e2)

and shiftTy ?(c=0) (d:int) = function
  | TVar m -> if (m < c) then TVar m else TVar (m+d)
  | TPi (x, t1, t2) -> TPi(x, shiftTy ~c:c d t1, shiftTy ~c:(c+1) d t2)
  | TApp (t, e) -> TApp(shiftTy ~c:c d t, shift ~c:c d e)

and shiftKind ?(c=0) (d:int) = function
  | KType -> KType
  | KPi (x, t1, k2) -> KPi(x, shiftTy ~c:c d t1, shiftKind ~c:(c+1) d k2)


let rec subst j e' = function
  | Var m -> if (j = m) then e' else Var m
  | Lambda (x,t,e) -> Lambda(x, substTy j e' t, subst j (shift 1 e') e)
  | App(e1, e2) -> App(subst j e' e1, subst j e' e2)

and substTy j e' = function
  | TVar m -> TVar m
  | TPi (x, t1, t2) -> TPi(x, substTy j e' t1, substTy j (shift 1 e') t2)
  | TApp (t, e) -> TApp(substTy j e' t, subst j e' e)

and substKind j e' = function
  | KType -> KType
  | KPi (x, t, k) -> KPi(x, substTy j e' t, substKind j (shift 1 e') k)



(*
let idsubst = Shift 0

(** [shift k e] shifts the indices in [e] by [k] places. *)
let shift k e = Subst (Shift k, e)

let mk_subst s e = Subst (s,e)

let mk_arrow t1 t2 = (TPi ("_", t1, shift 1 t2))

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
  let rec subst s e' =
    begin
      match s, e' with
      | Shift m, Var k -> Var (k + m)
      | Dot (a, s), Var 0 -> a
      | Dot (a, s), Var k -> subst s (Var (k - 1))
      | s, Subst (t, e) -> subst s (subst t e)
      | s, Lambda (x, t, e) ->
          let t = (match t with None -> None | Some t -> Some (mk_subst s t)) in
          let e = mk_subst (Dot (mk_var 0, compose (Shift 1) s)) e in
          Lambda (x, t, e)
      | s, App (e1, e2) -> App (mk_subst s e1, mk_subst s e2)
      | s, Ascribe (e, t) -> Ascribe (mk_subst s e, mk_subst s t)
      | s, (Type | Sort) -> e'
    end
  in
    subst

and substTy =
  let rec subst s t' =
    begin
      match s, t' with
      | s, Pi (x, t1, t2) ->
        let t1 = mk_subst s t1 in
        let t2 = mk_subst (Dot (mk_var 0, compose (Shift 1) s)) t2 in
          Pi (x, t1, t2)
      |

        and substKind =
  let rec subst s e' =
    match s, e' with
      | s, Pi (x, t1, t2) ->
        let t1 = mk_subst s t1 in
        let t2 = mk_subst (Dot (mk_var 0, compose (Shift 1) s)) t2 in
          Pi (x, t1, t2)

*)

(** [occurs v e] returns [true] when variable [Var v] occurs freely in [e]. *)
let rec occurs v e =
  match e with
    | Var m -> m = v
    (*| Subst (s, e) -> occurs v (subst s e)*)
    | Lambda (_, t, e) -> occursTy v t || occurs (v + 1) e
    | App (e1, e2) -> occurs v e1 || occurs v e2

and occursTy v t =
  match t with
    | TVar m -> m = v
    | TPi (_, t1, t2) -> occursTy v t1 || occursTy (v + 1) t2
    (*| Lambda (_, None, e) -> occurs (v + 1) e*)
    (*| Lambda (_, Some t, e) -> occurs v t || occurs (v + 1) e*)
    | TApp (t1, e2) -> occursTy v t1 || occurs v e2

and occursKind v k =
  match k with
    | KType -> false
    | KPi (_, t1, t2) -> occursTy v t1 || occursKind (v + 1) t2

(** Compare two expressions using alpha-equivalence only. *)
let rec equal e1 e2 =
  match e1, e2 with
  (*      | Subst (s, e1), _ -> equal (subst s e1loc) e2loc
          | _, Subst (s, e2) -> equal e1loc (subst s e2loc) *)
  | Var k, Var m -> k = m
  | Lambda (_, t1, e1), Lambda (_, t2, e2) -> equalTy t1 t2 && equal e1 e2
  | App (e11, e12), App (e21, e22) -> equal e11 e21 && equal e12 e22
  | (Var _ | Lambda _ | App _), _ -> false

and equalTy t1 t2 =
  match t1, t2 with
  | TVar k, TVar m -> k = m
  | TPi (_, t1, t2), TPi (_, t1', t2') -> equalTy t1 t1' && equalTy t2 t2'
  | TApp (t11, e12), TApp (t21, e22) -> equalTy t11 t21 && equal e12 e22
  | (TVar _ | TPi _ | TApp _), _ -> false

and equalKind k1 k2 =
  match k1, k2 with
  | KType, KType -> true
  | KPi (_, t11, k12), KPi(_, t21, k22) -> equalTy t11 t21 && equalKind k12 k22
  | (KType | KPi _), _ -> false


(*
let subst_operation s op =
  begin
    match op with
    | Inhabit t -> Inhabit (mk_subst s t)
  end

let rec subst_computation s =
  let rec subst s c =
    match c with
      | Return t -> Return (mk_subst s t)
      | Operation op -> Operation (subst_operation s op)
      | Let (x, c1, c2) ->
        let c1 = subst s c1 in
        let c2 = subst (Dot (Var 0, compose (Shift 1) s)) c2 in
          Let (x, c1, c2)
  in
    subst s

and subst_handler s lst = List.map (subst_handler_case s) lst

and subst_handler_case s (t, c) =
  let t = mk_subst s t in
  let c = subst_computation s c in
    (t, c)


let shift_computation k c = subst_computation (Shift k) c
*)

type operation =
  | InhabitTy of ty                   (* inhabit a type *)
  | InhabitKind of kind               (* inhabit a kind *)


(** Computations.
and computation =
  | Return of expr
  | ReturnTy of ty
  | Let of Common.variable * expr * computation
  *)
and computation = D.term

and handler = (operation * computation) list


let rec shiftOperation ?(c=0) d = function
  | InhabitTy ty -> InhabitTy (shiftTy ~c d ty)
  | InhabitKind kind -> InhabitKind (shiftKind ~c d kind)

