(** The Rio proof assistant language. *)

open Syntax

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
  | CheckWitness of term * sort
  | EqWitness of term * term * sort
  | TyJdg of term * sort
  | EqJdg of term * term * sort

and sort = term

type operation =
  | Inhabit of sort                   (* inhabit a sort *)
  | Infer of term                     (* infer the sort of expression *)
  | HasType of term * sort            (* inhabit a typing judgment *)
  | Equal of term * term * sort       (* inhabit judgmental equality *)

(** Computations. *)
type computation =
  | Let of Common.variable * computation * computation
  | Op of operation
  | CLambda of Common.variable * sort * computation

let rec infer_value ctx (v, loc) =
  match v with
    | Sort _ -> SortTy
    | Expr _ -> ExprTy
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
  
