(** Abstract syntax of TT *)

module StringMap = Map.Make(struct
                                type t = string
                                let compare = compare
                            end)


type universe = Universe.t

type eqsort =
  | Ju
  | Pr

type operation_tag = string

type tt_var = Common.name

type const =
  | Int of int
  | Bool of bool
  | Unit

type primop =
  | Plus
  | Not
  | And
  | Append

type exp = exp' * Position.t
and exp' =
  | Var of tt_var
  | Fun of tt_var * computation
  | Closure of tt_var * computation * exp StringMap.t
  | Handler of handler
  | ContExp of Context.t * Context.t * cont
  | Term   of Syntax.term
  | Type   of Syntax.ty
  | Tuple  of exp list
  | Const  of const
  | Inj    of int * exp
  | DefaultHandler

and computation = computation' * Position.t
and computation' =
  | Val of exp
  | App of exp * exp
  | Let of tt_var * computation * computation
  | Op  of operation_tag * exp
  | WithHandle of exp * computation
  (*| KApp of exp * exp*)
  | Ascribe of exp * exp
  | Prim of primop * exp list
  | Match of exp * arm list
  | Check of Syntax.ty * Syntax.ty * exp * computation
  | MkVar of int
  | MkLam of Common.name * exp * computation
  (*| MkApp of exp * exp*)

and cont =
  | KHole
  | KLet of tt_var * cont * computation
  | KWithHandle of exp * cont
  | KMkLam of Common.name * Syntax.ty * cont

and arm = pattern * computation

and handler =
  {
    valH : tt_var * computation;
    opH  : (operation_tag * pattern * tt_var * computation) list;
    finH : (tt_var * computation) option;
  }

and pattern =
  | PTuple of tt_var list
  | PInj of int * tt_var
  | PConst of const
  | PVar of tt_var
  | PWild

and result =
  | RVal of exp
  | ROp of operation_tag * Context.t * exp * cont

type toplevel = toplevel' * Position.t
and toplevel' =
  | TopLet of Common.name * computation
  | TopDef of Common.name * computation
  | TopParam of Common.name list * computation
  | TopEval of computation
  | Context
  | Help
  | Quit

(** String conversion functions to be used only for debugging where proper printing of
    terms is not available. *)

let embrace s = "(" ^ s ^ ")"
let tag h lst = h ^ embrace (String.concat ", " lst)

let string_of_primop = function
  | Plus -> "Plus"
  | Not -> "Not"
  | And -> "And"
  | Append -> "Append"

let rec string_of_exp (exp, _loc) =
  match exp with
  | Var x -> tag "Var" [x]
  | Fun (x,c) -> tag "Fun" [x; string_of_computation c]
  | Closure (x,c,_) -> tag "Closure" [x; string_of_computation c; "-"]
  | Handler h -> tag "Handler" [string_of_handler h]
  | ContExp (_gamma,_delta,k) -> tag "ContExp" ["-"; "-"; string_of_cont k]
  | Term _b -> "<term>"
  | Type _t -> "<type>"
  | Tuple es -> tag "Tuple" (List.map string_of_exp es)
  | Const c -> string_of_const c
  | Inj (i,e) -> tag "Inj" [string_of_int i; string_of_exp e]
  | DefaultHandler -> "default"

and string_of_computation (comp, _loc) =
  match comp with
  | Val e -> string_of_exp e
  | App (e1, e2) -> tag "App" [string_of_exp e1; string_of_exp e2]
  | Let (x,c1,c2) -> tag "Let" [x;
                                string_of_computation c1;
                                string_of_computation c2]
  | Op (op, e) -> tag "Op" [op; string_of_exp e]
  | WithHandle (e,c) -> tag "WithHandle" [string_of_exp e; string_of_computation c]
  (*| KApp (e1, e2) -> tag "KApp" [string_of_exp e1; string_of_exp e2]*)
  | Ascribe (e1, e2) -> tag "Ascribe" [string_of_exp e1; string_of_exp e2]
  | Prim (op, es) -> tag "Prim" (string_of_primop op :: List.map string_of_exp es)
  | Match (e, arms) -> tag "match" (string_of_exp e ::
                                    List.map string_of_arm arms)
  | Check (t1, t2, e, c) -> tag "Check" ["<type 1>"; "<type 2>"; string_of_exp e;
                                          string_of_computation c]
  | MkVar n -> tag "MkVar" [string_of_int n]
  | MkLam (x,e,c) -> tag "MkLam" [x; string_of_exp e; string_of_computation c]
  (*| MkApp (e1, e2) -> tag "MkApp" [string_of_exp e1; string_of_exp e2]*)

and string_of_cont k =
  match k with
  | KHole -> "KHole"
  | KLet (x,k,c) -> tag "KLet" [x; string_of_cont k;
                                string_of_computation c]
  | KWithHandle (e,k) -> tag "KWithHandle" [string_of_exp e; string_of_cont k]
  | KMkLam (x,t,k) -> tag "KMkLam" [x; "<type>"; string_of_cont k]

and string_of_arm (p,c) = tag "" [string_of_pat p; string_of_computation c]

and string_of_handler _ = "<handler>"

(*and string_of_case (op, terms, c) =*)
    (*tag op  (List.map to_str terms) ^ " => " ^ to_str c*)
  (*in*)
    (*to_str*)

and string_of_pat = function
  | PTuple xs -> tag "PTuple" xs
  | PInj (i,x) -> tag "PInj" [string_of_int i; x]
  | PConst c -> tag "PConst" [string_of_const c]
  | PVar v -> tag "PVar" [v]
  | PWild -> "PWild"

and string_of_const = function
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "()"

let print exp =
  print_endline (string_of_exp exp)

(************)
(* Shifting *)
(************)

let rec shift cut delta (exp, loc) =
  (match exp with
  | Var v -> exp
  | Fun (x, c) -> Fun(x, shift_computation cut delta c)
  | Closure (x, c, eta) -> Closure(x, shift_computation cut delta c,
                               StringMap.map (shift cut delta) eta)
  | Handler h -> Handler (shift_handler cut delta h)
  | ContExp(delta, gamma, k) ->
      Error.syntax ~loc "Cannot shift a continuation"
  | Term b -> Term (Syntax.shift ~bound:cut delta b)
  | Type t -> Type (Syntax.shift_ty ~bound:cut delta t)
  | Tuple exps -> Tuple (List.map (shift cut delta) exps)
  | Const _ -> exp
  | DefaultHandler -> exp
  | Inj (i, exp2) -> Inj(i, shift cut delta exp2)),
  loc

and shift_computation cut delta (comp, loc) =
  let recur = shift cut delta in
  let recurc = shift_computation cut delta in
  (match comp with
  | Val e -> Val (recur e)
  | App (e1, e2) -> App(recur e1, recur e2)
  | Let (x,c1,c2) -> Let(x, recurc c1, recurc c2)
  | Op (op, e) -> Op(op, recur e)
  | WithHandle(e,c) -> WithHandle(recur e, recurc c)
  (*| KApp(e1,e2) -> KApp(recur e1, recur e2)*)
  | Ascribe(e1,e2) -> Ascribe(recur e1, recur e2)
  | Prim(op, es) -> Prim(op, List.map recur es)
  | Match(e, pcs) -> Match(recur e,
                           List.map (fun (p,c) -> (p, recurc c)) pcs)
  | Check (t1, t2, e, c) -> Check (Syntax.shift_ty ~bound:cut delta t1,
                                   Syntax.shift_ty ~bound:cut delta t2,
                                   recur e, recurc c)
  | MkVar _n -> comp
  | MkLam(x,e,c) -> MkLam(x, recur e, recurc c)
  (*| MkApp(e1,e2) -> MkApp(recur e1, recur e2)*)
  ), loc

and shift_handler cut delta {valH=(xv,cv); opH; finH} =
  let shift_case (tag, xs, k, c) = (tag, xs, k, shift_computation cut delta c)  in
  {
    valH = (xv, shift_computation cut delta cv);
    opH = List.map shift_case opH;
    finH = (match finH with
              None -> None
            | Some (xf,cf) -> Some (xf, shift_computation cut delta cf));
  }

(****************)
(* Substitution *)
(****************)

let bound_in_pat var = function
  | PTuple xs -> List.mem var xs
  | PInj(_, x) -> var = x
  | PVar x -> var = x
  | PWild -> false
  | PConst _ -> false


let rec psubst ?(bvs=0) sigma exp1 =
  let recur = psubst ~bvs sigma in
  let recurk = psubst_continuation ~bvs sigma  in
  match exp1 with
  | Var x1, loc ->
      if List.mem_assoc x1 sigma then
        List.assoc x1 sigma
      else
        shift 0 bvs exp1
  | Fun (x1, c2), loc ->
      let sigma' = List.remove_assoc x1 sigma in
      Fun(x1, psubst_computation ~bvs sigma' c2), loc
  | Closure (x1, c2, eta), loc ->
      let eta' = StringMap.map (psubst ~bvs sigma) eta  in
      let sigma = List.remove_assoc x1 sigma in
      let sigma = List.filter (fun (k,_) -> not (StringMap.mem k eta)) sigma in
      Closure(x1, psubst_computation ~bvs sigma c2, eta'), loc
  | Handler h, loc -> Handler (psubst_handler ~bvs sigma h), loc
  | ContExp(delta, gamma, k), loc -> ContExp(delta, gamma, recurk k), loc
  | Term _b, loc -> exp1
  | Type _t, loc -> exp1
  | Tuple es, loc -> Tuple(List.map recur es), loc
  | Const _c, loc -> exp1
  | DefaultHandler, loc -> exp1
  | Inj(i1, exp2), loc -> Inj(i1, recur exp2), loc

and psubst_computation ?(bvs=0) sigma (comp1, loc) =
  let recur = psubst ~bvs sigma in
  let recurc = psubst_computation ~bvs sigma  in
  (match comp1 with
  | Val e -> Val (recur e)
  | App (e1, e2) -> App (recur e1, recur e2)
  | Let (x, c1, c2) ->
      let c1' = recurc c1  in
      let sigma' = List.remove_assoc x sigma  in
      let c2' = psubst_computation ~bvs sigma' c2  in
      Let (x, c1', c2')
  | Op (op, e) -> Op (op, recur e)
  | WithHandle(e,c) -> WithHandle(recur e, recurc c)
  (*| KApp (e1, e2) -> KApp (recur e1, recur e2)*)
  | Ascribe (e1, e2) -> Ascribe (recur e1, recur e2)
  | Prim (op, es) -> Prim(op, List.map recur es)
  | Match(e, pcs) -> Match(recur e, List.map (psubst_arm ~bvs sigma) pcs)
  | Check(t1, t2, e, c) -> Check(t1, t2, recur e, recurc c)
  | MkVar _n -> comp1
  | MkLam (x, e, c) ->
      let e' = recur e  in
      let sigma' = List.remove_assoc x sigma in
      let c' = psubst_computation ~bvs:(bvs+1) sigma' c  in
      MkLam(x, e', c')
  (*| MkApp (e1, e2) -> MkApp (recur e1, recur e2)*)
  ), loc

and psubst_handler ?(bvs=0) sigma {valH=(xv,cv); opH; finH} =
  let subst_case (tag, p, k, c) =
    let unshadowed (v,_) = not (bound_in_pat v p || v = k)  in
    let sigma = List.filter unshadowed sigma  in
      (tag, p, k, psubst_computation ~bvs sigma c)  in
  {
    valH = (xv, psubst_computation ~bvs (List.remove_assoc xv sigma) cv);
    opH = List.map subst_case opH;
    finH = (match finH with
              None -> None
            | Some (xf,cf) -> Some (xf, psubst_computation ~bvs (List.remove_assoc xf sigma) cf));
  }

and psubst_continuation ?(bvs=0) sigma k =
  let recur  = psubst ~bvs sigma in
  let recurk = psubst_continuation ~bvs sigma in
  match k with
    | KHole -> k
    | KLet (x,k,c) ->
        let k' = recurk k  in
        let sigma' = List.remove_assoc x sigma  in
        let c' = psubst_computation ~bvs sigma' c  in
        KLet(x, k', c')
    | KWithHandle(e, k) -> KWithHandle(recur e, recurk k)
    | KMkLam(x,t,k) ->
        let sigma' = List.remove_assoc x sigma  in
        KMkLam(x, t, psubst_continuation ~bvs:(bvs+1) sigma' k)

and psubst_arm ~bvs sigma (pat, comp) =
  let unshadowed (v,_) = not (bound_in_pat v pat)  in
  let sigma' = List.filter unshadowed sigma  in
  (pat, psubst_computation ~bvs sigma' comp)

and subst_computation x2 e2 = psubst_computation [(x2,e2)]

(****************)
(* Hole-filling *)
(****************)


(* Not capture-avoiding! *)

let rec kfill ((_, loc) as exp) = function
  | KHole -> Val exp, loc
  | KLet (x,k,c) -> Let(x, kfill exp k, c), Position.nowhere
  | KWithHandle(e, k) -> WithHandle(e, kfill exp k), Position.nowhere
  | KMkLam(x, t, k) -> MkLam(x, (Type t, snd t), kfill exp k), Position.nowhere

