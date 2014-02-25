(** Abstract syntax of internal expressions. *)

module D = Input

(** Abstract syntax of expressions, where de Bruijn indices are used to represent
    variables. *)
type expr =
  | Var of int
  | Lambda of Common.variable * ty * expr
  | App of expr * expr
  | Pair of expr * expr
  | Proj of int * expr (* 1 = fst, 2 = snd *)
  | Refl of expr * ty         (* : TEquiv(e,e,t) *)
  | ReflTy of ty * kind       (* : TEquivTy(t,t,k) *)

and ty =
  | TVar of int
  | TPi of Common.variable * ty * ty
  | TSigma of Common.variable * ty * ty
  | TApp of ty * expr
  | TEquiv of expr * expr * ty                (* equivalence of terms *)
  | TEquivTy of ty * ty * kind                (* equivalnece of types *)

and kind =
  | KType
  | KPi of Common.variable * ty * kind

  (*
(** Explicit substitutions. *)
and substitution =
  | Shift of int
  | Dot of expr * substitution
  *)

let rec string_of_expr = function
  | Var i -> string_of_int i
  | Lambda(x,t,e) -> "Lambda(" ^ x ^ "," ^ string_of_ty t ^ "," ^ string_of_expr e ^ ")"
  | App(e1,e2) -> "App(" ^ string_of_expr e1 ^ "," ^ string_of_expr e2 ^ ")"
  | Pair(e1,e2) -> "Pair(" ^ string_of_expr e1 ^ "," ^ string_of_expr e2 ^ ")"
  | Proj(i1,e2) -> "Proj(" ^ string_of_int i1 ^ "," ^ string_of_expr e2 ^ ")"
  | Refl(e,t) -> "Refl(" ^ string_of_expr e ^ "," ^ string_of_ty t ^")"
  | ReflTy(t,k) -> "Refl(" ^ string_of_ty t ^ "," ^ string_of_kind k ^")"

and string_of_ty = function
  | TVar i -> string_of_int i
  | TPi(x,t,t') -> "TPi(" ^ x ^ "," ^ string_of_ty t ^ "," ^ string_of_ty t' ^ ")"
  | TSigma(x,t,t') -> "TSigma(" ^ x ^ "," ^ string_of_ty t ^ "," ^ string_of_ty t' ^ ")"
  | TApp(t1,e2) -> "TApp(" ^ string_of_ty t1 ^ "," ^ string_of_expr e2 ^ ")"
  | TEquiv(e1, e2, t) -> "TEquiv(" ^ string_of_expr e1 ^ "," ^ string_of_expr e2
                            ^ "," ^ string_of_ty t ^ ")"
  | TEquivTy(t1, t2, k) -> "TEquivTy(" ^ string_of_ty t1 ^ "," ^ string_of_ty t2
                            ^ "," ^ string_of_kind k ^ ")"

and string_of_kind = function
  | KType -> "Type"
  | KPi(x,t,k) -> "KPi(" ^ x ^ "," ^ string_of_ty t ^ "," ^ string_of_kind k ^ ")"



  (** [shift c d] shifts the indices by [d] with a cutoff of [c]. *)
  (* See, e.g., http://ecee.colorado.edu/~siek/ecen5013/spring10/lecture4.pdf *)

let rec shift ?(c=0) d = function
  | Var m -> if (m < c) then Var m else Var(m+d)
  | Lambda (x, t, e) -> Lambda (x, shiftTy ~c d t, shift ~c:(c+1) d e)
  | App (e1, e2) -> App(shift ~c d e1, shift ~c d e2)
  | Pair (e1, e2) -> Pair(shift ~c d e1, shift ~c d e2)
  | Proj (i1, e2) -> Proj(i1, shift ~c d e2)
  | Refl (e, t) -> Refl(shift ~c d e, shiftTy ~c d t)
  | ReflTy (t, k) -> ReflTy(shiftTy ~c d t, shiftKind ~c d k)

and shiftTy ?(c=0) (d:int) = function
  | TVar m -> if (m < c) then TVar m else TVar (m+d)
  | TPi (x, t1, t2) -> TPi(x, shiftTy ~c d t1, shiftTy ~c:(c+1) d t2)
  | TSigma (x, t1, t2) -> TSigma(x, shiftTy ~c d t1, shiftTy ~c:(c+1) d t2)
  | TApp (t, e) -> TApp(shiftTy ~c d t, shift ~c d e)
  | TEquiv (e1, e2, t) -> TEquiv(shift ~c d e1, shift ~c d e2, shiftTy ~c d t)
  | TEquivTy (t1, t2, k) -> TEquivTy(shiftTy ~c d t1, shiftTy ~c d t2, shiftKind ~c d k)

and shiftKind ?(c=0) (d:int) = function
  | KType -> KType
  | KPi (x, t1, k2) -> KPi(x, shiftTy ~c d t1, shiftKind ~c:(c+1) d k2)


let rec subst j e' = function
  | Var m -> if (j = m) then e' else Var m
  | Lambda (x,t,e) -> Lambda(x, substTy j e' t, subst (j+1) (shift 1 e') e)
  | App(e1, e2) -> App(subst j e' e1, subst j e' e2)
  | Pair(e1, e2) -> Pair(subst j e' e1, subst j e' e2)
  | Proj(i1, e2) -> Proj(i1, subst j e' e2)
  | Refl(e, t) -> Refl(subst j e' e, substTy j e' t)
  | ReflTy(t, k) -> ReflTy(substTy j e' t, substKind j e' k)

and substTy j e' = function
  | TVar m -> TVar m
  | TPi (x, t1, t2) -> TPi(x, substTy j e' t1, substTy (j+1) (shift 1 e') t2)
  | TSigma (x, t1, t2) -> TSigma(x, substTy j e' t1, substTy (j+1) (shift 1 e') t2)
  | TApp (t, e) -> TApp(substTy j e' t, subst j e' e)
  | TEquiv(e1, e2, t) -> TEquiv(subst j e' e1, subst j e' e2, substTy j e' t)
  | TEquivTy(t1, t2, k) -> TEquivTy(substTy j e' t1, substTy j e' t2, substKind j e' k)

and substKind j e' = function
  | KType -> KType
  | KPi (x, t, k) -> KPi(x, substTy j e' t, substKind (j+1) (shift 1 e') k)


and beta eBody eArg =
  shift (-1) (subst 0 (shift 1 eArg) eBody)

and betaTy tBody eArg =
  (*let _ = Printf.printf "betaTy\ntBody = %s\neArg = %s\n"*)
             (*(string_of_ty tBody) (string_of_expr eArg)  in*)
  let shiftArg = shift 1 eArg in
  (*let _ = Printf.printf "shiftArg = %s\n" (string_of_expr shiftArg)  in*)
  let afterSubst = substTy 0 shiftArg tBody in
  (*let _ = Printf.printf "afterSubst = %s\n" (string_of_ty afterSubst)  in*)
  let answer = shiftTy (-1) afterSubst  in
  (*let _ = Printf.printf "answer = %s\n\n" (string_of_ty answer)  in*)
  answer

and betaKind kBody eArg =
  shiftKind (-1) (substKind 0 (shift 1 eArg) kBody)

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
    | Pair (e1, e2) -> occurs v e1 || occurs v e2
    | Proj (_, e2) -> occurs v e2
    | Refl (e, t) -> occurs v e || occursTy v t
    | ReflTy (t, k) -> occursTy v t || occursKind v k

and occursTy v t =
  match t with
    | TVar m -> m = v
    | TPi (_, t1, t2) -> occursTy v t1 || occursTy (v + 1) t2
    | TSigma (_, t1, t2) -> occursTy v t1 || occursTy (v + 1) t2
    (*| Lambda (_, None, e) -> occurs (v + 1) e*)
    (*| Lambda (_, Some t, e) -> occurs v t || occurs (v + 1) e*)
    | TApp (t1, e2) -> occursTy v t1 || occurs v e2
    | TEquiv (e1, e2, t) -> occurs v e1 || occurs v e2 || occursTy v t
    | TEquivTy (t1, t2, k) -> occursTy v t1 || occursTy v t2 || occursKind v k

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
  | Pair (e11, e12), Pair (e21, e22) -> equal e11 e21 && equal e12 e22
  | Proj (i11, e12), Proj (i21, e22) -> i11 = i21 && equal e12 e22
  | Refl (e1, t1), Refl (e2, t2) -> equal e1 e2 && equalTy t1 t2
  | ReflTy (t1, k1), ReflTy (t2, k2) -> equalTy t1 t2 && equalKind k1 k2
  | (Var _ | Lambda _ | App _ | Pair _ | Proj _ | Refl _ | ReflTy _), _ -> false

and equalTy t1 t2 =
  match t1, t2 with
  | TVar k, TVar m -> k = m
  | TPi (_, t1, t2), TPi (_, t1', t2') -> equalTy t1 t1' && equalTy t2 t2'
  | TSigma (_, t1, t2), TSigma (_, t1', t2') -> equalTy t1 t1' && equalTy t2 t2'
  | TApp (t11, e12), TApp (t21, e22) -> equalTy t11 t21 && equal e12 e22
  | TEquiv(e11, e12, t1), TEquiv(e21, e22, t2) ->
      equal e11 e21 && equal e12 e22 && equalTy t1 t2
  | TEquivTy(t11, t12, k1), TEquivTy(t21, t22, k2) ->
      equalTy t11 t21 && equalTy t12 t22 && equalKind k1 k2
  | (TVar _ | TPi _ | TApp _ | TSigma _ | TEquiv _ | TEquivTy _), _ -> false

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
  | Coerce of ty * ty                 (* t1 >-> t2 *)


(** Computations.
and computation =
  | Return of expr
  | ReturnTy of ty
  | Let of Common.variable * expr * computation
  *)
and computation = Common.debruijn D.term

and handler = (operation * computation) list


let rec shiftOperation ?(c=0) d = function
  | InhabitTy ty -> InhabitTy (shiftTy ~c d ty)
  | InhabitKind kind -> InhabitKind (shiftKind ~c d kind)
  | Coerce (ty1, ty2) -> Coerce (shiftTy ~c d ty1, shiftTy ~c d ty2)

