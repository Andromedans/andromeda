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
  | Eq
  | Neq

type environment = (value * int) StringMap.t

(* Closed values *)
and value = value' * Position.t
and value' =
  | VFun     of tt_var * computation * environment
  | VHandler of handler * environment
  | VCont    of Context.t * Context.t * (value -> computation) * environment
  | VTuple   of value list
  | VConst   of const
  | VInj     of int * value
  | VTerm   of Syntax.term
  | VType   of Syntax.ty

and exp = exp' * Position.t
and exp' =
  | Value of value
  | Var of tt_var
  | Fun of tt_var * computation
  | Handler of handler
  | Tuple  of exp list
  | Const  of const
  | Inj    of int * exp
  | Term   of Syntax.term
  | Type   of Syntax.ty
  | Prim of primop * exp list

and computation = computation' * Position.t
and computation' =
  | Return of exp
  | App of exp * exp
  | Let of tt_var * computation * computation
  | Op  of operation_tag * exp
  | WithHandle of exp * computation
  | Ascribe of exp * exp
  | Match of exp * arm list
  | Check of Syntax.ty * Syntax.ty * exp * computation
  | MkVar of int
  | MkLam of Common.name * exp * computation
  | BrazilTermCode of string
  | BrazilTypeCode of string

and arm = pattern * computation

and handler =
  {
    valH : (tt_var * computation) option;
    opH  : (operation_tag * pattern * tt_var * computation) list;
    finH : (tt_var * computation) option;
  }

and pattern =
  | PTuple of pattern list
  | PInj of int * pattern
  | PConst of const
  | PVar of tt_var
  | PWild

and result =
  | RVal of value
  | ROp of operation_tag * Context.t * value * ((value -> computation) * environment)

type toplevel = toplevel' * Position.t
and toplevel' =
  | TopLet of Common.name * computation
  | TopDef of Common.name * computation
  | TopParam of Common.name list * computation
  | TopEval of computation
  | Context
  | Help
  | Quit


let mkApp ?(loc=Position.nowhere) e1 e2 = App (e1, e2), loc
let mkAscribe ?(loc=Position.nowhere) e1 e2 = Ascribe (e1,e2), loc
let mkCheck ?(loc=Position.nowhere) t1 t2 e c = Check (t1,t2,e,c), loc
let mkConst ?(loc=Position.nowhere) const = Const const, loc
let mkHandler ?(loc=Position.nowhere) h = Handler h, loc
let mkLet ?(loc=Position.nowhere) x c1 c2 = Let (x,c1,c2), loc
let mkMkLam ?(loc=Position.nowhere) x e c = MkLam (x,e,c), loc
let mkOp ?(loc=Position.nowhere) op arg = Op(op, arg), loc
let mkReturn ?(loc=Position.nowhere) e = Return e, loc
let mkTerm ?(loc=Position.nowhere) term = Term term, loc
let mkTuple ?(loc=Position.nowhere) es = Tuple es, loc
let mkType ?(loc=Position.nowhere) ty = Type ty, loc
let mkVar ?(loc=Position.nowhere) e = Var e, loc
let mkValue ?(loc=Position.nowhere) v = Value v, loc
let mkWithHandle ?(loc=Position.nowhere) e c = WithHandle (e, c), loc


let mkVCont ?(loc=Position.nowhere) g d k eta = VCont (g,d,k,eta), loc
let mkVConst ?(loc=Position.nowhere) a = VConst a, loc
let mkVHandler ?(loc=Position.nowhere) h eta = VHandler (h,eta), loc
let mkVInj ?(loc=Position.nowhere) i v = VInj(i,v), loc
let mkVTerm ?(loc=Position.nowhere) term = VTerm term, loc
let mkVTuple ?(loc=Position.nowhere) es = VTuple es, loc
let mkVType ?(loc=Position.nowhere) ty = VType ty, loc



(** String conversion functions to be used only for debugging where proper printing of
    terms is not available. *)

let embrace s = "(" ^ s ^ ")"
let tag h lst = h ^ embrace (String.concat ", " lst)

let string_of_primop = function
  | Plus -> "Plus"
  | Not -> "Not"
  | And -> "And"
  | Append -> "Append"
  | Eq -> "Eq"
  | Neq -> "Neq"

let rec string_of_exp ctx (exp, _loc) =
  let recur = string_of_exp ctx  in
  let recurc = string_of_computation ctx  in
  match exp with
  | Var x -> tag "Var" [x]
  | Value value -> tag "Value" []
  | Fun (x,c) -> tag "Fun" [x; recurc c]
  | Handler h -> tag "Handler" [string_of_handler ctx h]
  | Term b -> tag "Term" [string_of_term ctx b]
  | Type t -> tag "Type" [string_of_ty ctx t]
  | Tuple es -> tag "Tuple" (List.map recur es)
  | Const c -> string_of_const c
  | Inj (i,e) -> tag "Inj" [string_of_int i; recur e]
  | Prim (op, es) -> tag "Prim" (string_of_primop op :: List.map recur es)

and string_of_computation ctx (comp, _loc) =
  let recur = string_of_exp ctx  in
  let recurc = string_of_computation ctx  in
  match comp with
  | Return e -> recur e
  | App (e1, e2) -> tag "App" [recur e1; recur e2]
  | Let (x,c1,c2) -> tag "Let" [x; recurc c1; recurc c2]
  | Op (op, e) -> tag "Op" [op; recur e]
  | WithHandle (e,c) -> tag "WithHandle" [recur e; recurc c]
  (*| KApp (e1, e2) -> tag "KApp" [recur e1; recur e2]*)
  | Ascribe (e1, e2) -> tag "Ascribe" [recur e1; recur e2]
  | Match (e, arms) -> tag "match" (recur e ::
                                    List.map (string_of_arm ctx) arms)
  | Check (t1, t2, e, c) -> tag "Check" ["<type 1>"; "<type 2>"; recur e;
                                          recurc c]
  | MkVar n -> tag "MkVar" [string_of_int n]
  | MkLam (x,e,c) ->
      (* XXX: Need to add x to the context! *)
      let dummy_ty = (Syntax.Unit, Position.nowhere)  in
      tag "MkLam" [x; recur e; string_of_computation (Context.add_var x dummy_ty ctx ) c]
  (*| MkApp (e1, e2) -> tag "MkApp" [recur e1; recur e2]*)
  | BrazilTermCode s -> "`" ^ s ^ "`"
  | BrazilTypeCode s -> "t`" ^ s ^ "`"

and string_of_value ctx (value, _loc) =
  let recurv = string_of_value ctx  in
  let recurc = string_of_computation ctx  in
  let recurk = string_of_cont ctx  in
  match value with
  | VFun(x,c,_eta) -> tag "VFun" [x; recurc c; "-"]
  | VHandler(h,_eta) -> tag "VHandler" [string_of_handler ctx h; "-"]
  | VCont (_delta,_gamma, k, _eta) -> tag "VCont" ["?"; "?"; recurk k; "?"]
  | VTuple vs -> tag "VTuple" (List.map recurv vs)
  | VConst a -> tag "VConst" [string_of_const a]
  | VInj (i,v) -> tag "VInj" [string_of_int i; recurv v]
  | VTerm b -> tag "VTerm" [string_of_term ctx b]
  | VType t -> tag "VType" [string_of_ty ctx t]


and string_of_cont ctx k =
  "cont"

and string_of_arm ctx (p,c) = tag "" [string_of_pat p; string_of_computation ctx c]

and string_of_handler ctx _ = "<handler>"

(*and string_of_case (op, terms, c) =*)
    (*tag op  (List.map to_str terms) ^ " => " ^ to_str c*)
  (*in*)
    (*to_str*)

and string_of_pat = function
  | PTuple ps -> tag "PTuple" (List.map string_of_pat ps)
  | PInj (i,p) -> tag "PInj" [string_of_int i; string_of_pat p]
  | PConst c -> tag "PConst" [string_of_const c]
  | PVar v -> tag "PVar" [v]
  | PWild -> "PWild"

and string_of_const = function
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "()"

and string_of_term ctx term =
  ignore (Format.flush_str_formatter ());
  Print.print Format.str_formatter "%t" (Print.term (Context.names ctx) term);
  Format.flush_str_formatter ()

and string_of_ty ctx ty =
  ignore (Format.flush_str_formatter ());
  Print.print Format.str_formatter "%t" (Print.ty (Context.names ctx) ty);
  Format.flush_str_formatter ()

and string_of_eta ctx eta =
  let binds = StringMap.bindings eta  in
  let string_of_bind (x, _) = x ^ "= ?" in
  let strings = List.map string_of_bind binds  in
  "[" ^ (String.concat ", " strings) ^ "]"


(************)
(* Shifting *)
(************)

let rec shift cut delta (exp, loc) =
  if delta = 0 then (exp,loc) else
  (let recur = shift cut delta in
   let recurv = shiftv cut delta in
   let recurc = shift_computation cut delta in
   (match exp with
  | Var v -> exp
  | Value value -> Value (recurv value)
  | Fun (x, c) -> Fun(x, recurc c)
  | Handler h -> Handler (shift_handler cut delta h)
  | Term b -> Term (Syntax.shift ~bound:cut delta b)
  | Type t -> Type (Syntax.shift_ty ~bound:cut delta t)
  | Tuple exps -> Tuple (List.map recur exps)
  | Const _ -> exp
  | Inj (i, exp2) -> Inj(i, recur exp2)
  | Prim(op, es) -> Prim(op, List.map recur es)
   ), loc)

and shiftv cut delta (value, loc) =
  if delta = 0 then (value,loc) else
  (let recurv = shiftv cut delta in
   let recurc = shift_computation cut delta in
  (match value with
  | VFun(x, c, eta) -> VFun(x, recurc c, eta)
  | VHandler (h, eta) -> VHandler (shift_handler cut delta h, eta)
  | VCont _ -> Error.runtime ~loc "shiftv: Cannot shift a continuation"
  | VTuple vs -> VTuple (List.map recurv vs)
  | VConst _ -> value
  | VInj (i,v) -> VInj(i, recurv v)
  | VTerm b -> VTerm (Syntax.shift ~bound:cut delta b)
  | VType t -> VType (Syntax.shift_ty ~bound:cut delta t)),
  loc)

and shift_computation cut delta (comp, loc) =
  if delta = 0 then (comp,loc) else
  (let recur = shift cut delta in
  let recurc = shift_computation cut delta in
  (match comp with
  | Return e -> Return (recur e)
  | App (e1, e2) -> App(recur e1, recur e2)
  | Let (x,c1,c2) -> Let(x, recurc c1, recurc c2)
  | Op (op, e) -> Op(op, recur e)
  | WithHandle(e,c) -> WithHandle(recur e, recurc c)
  (*| KApp(e1,e2) -> KApp(recur e1, recur e2)*)
  | Ascribe(e1,e2) -> Ascribe(recur e1, recur e2)
  | Match(e, pcs) -> Match(recur e,
                           List.map (fun (p,c) -> (p, recurc c)) pcs)
  | Check (t1, t2, e, c) -> Check (Syntax.shift_ty ~bound:cut delta t1,
                                   Syntax.shift_ty ~bound:cut delta t2,
                                   recur e, recurc c)
  | MkVar _n -> comp
  | MkLam(x,e,c) -> MkLam(x, recur e, shift_computation (cut+1) delta c)
  | BrazilTermCode s -> Error.runtime ~loc "Unimplemented: shifting of BrazilTermCode"
  | BrazilTypeCode s -> Error.runtime ~loc "Unimplemented: shifting of BrazilTypeCode"
  (*| MkApp(e1,e2) -> MkApp(recur e1, recur e2)*)
  ), loc)

and shift_handler cut delta ({valH; opH; finH} as h) =
  if delta = 0 then h else
  (let shift_case (tag, xs, k, c) = (tag, xs, k, shift_computation cut delta c)  in
  {
    valH = (match valH with
              None -> None
            | Some (xv,cv) -> Some (xv, shift_computation cut delta cv));
    opH = List.map shift_case opH;
    finH = (match finH with
              None -> None
            | Some (xf,cf) -> Some (xf, shift_computation cut delta cf));
  })

(* Equality *)

let rec eqvalue value1 value2 =
  match fst value1, fst value2 with
  | VTuple vs1, VTuple vs2 -> List.for_all2 eqvalue vs1 vs2
  | VConst a1, VConst a2 -> a1 = a2
  | VInj (i1,v1), VInj(i2,v2) -> i1 = i2 && eqvalue v1 v2
  | VTerm b1, VTerm b2 -> Syntax.equal b1 b2
  | VType t1, VType t2 -> Syntax.equal_ty t1 t2
  | (VFun _ | VHandler _ | VCont _ | VTuple _ | VConst _ |
     VInj _ | VTerm _ | VType _), _ -> false

