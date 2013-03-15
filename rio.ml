open Syntax

type operation =
  | Infer of expr                     (* infer the type of expression (only small ones) *)
  | Check of expr * ty                (* check that expression has type *)
  | Equal of ty * expr * expr         (* inhabit equality type *)

(** Computation types are types of results of computations. *)
type ty =
  | ExprTy
  | SortTy                      (* result of infer *)
  | Checked of expr * ty        (* result of checking *)
  | Equated of ty * expr * expr (* result of verifying an equation *)

type value =
  | Sort of expr
  | Expr of expr
  | Sym of value (* symmetry *)
  | EqualWitness of ty * expr * expr
  | CheckWitness of expr * ty
 
(** Computations, currently a very limited version. *)
type computation =
  | Return of value
  | Let of Common.variable * computation * computation
  | Op of operation

let rec infer_value ctx (v, loc) =
  match v with
    | Sort _ -> SortTy
    | Expr _ -> ExprTy
    | Sym v ->
      (match infer_value ctx v with
        | Equated (t, e1, e2) -> Equated (t, e2, e1)
        | _ -> Error.typing ~loc "this expression is %t
      
  | EqualWitness (t, e1, e2) -> Equal (t, e1, e2)
  | CheckWitness (e, t) -> Check (false, e, t)

let infer_op ctx =
  | Infer _ -> SortTy
  | Check (e, t) -> Checked (e, t)
  | Equal (t, e1, e2) -> Equated (t, e1, e2)

let rec infer_comp ctx = function
  | Return v -> infer_value ctx v
  | Let (x, c1, c2) ->
    let t1 = infer_comp ctx c1 in
      infer_comp ((x,c1) :: ctx) c2
  | Op op -> infer_op ctx op
  
