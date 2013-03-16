(** Abstract syntax of input files. *)

(** Abstract syntax of expressions as given by the user. *)
type expr = expr' * Common.position
and expr' =
  | Var of Common.variable
  | Type
  | Pi of Common.variable * sort * expr
  | Lambda of Common.variable * sort option * expr
  | App of expr * expr
  | Ascribe of expr * sort
  | TyJdg of expr * sort
  | EqJdg of expr * expr * sort

and sort = expr

type operation = operation' * Common.position
and operation' =
  | Inhabit of sort
  | Infer of expr
  | HasType of expr * sort
  | Equal of expr * expr * sort

type computation = computation' * Common.position
and computation' = ((Common.variable * sort) * Common.position) list * operation

(** Toplevel directives. *)
type directive = directive' * Common.position
and directive' =
  | Quit
  | Help
  | Context
  | Eval of expr

type toplevel = toplevel' * Common.position
and toplevel' =
  | Computation of computation
  | TopLet of Common.variable * computation
  | TopParam of Common.variable * sort
  | Context
  | Eval of expr
  | Help
  | Quit

