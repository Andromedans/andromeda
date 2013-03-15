(** Abstract syntax of input files. *)

(** Abstract syntax of expressions as given by the user. *)
type expr = expr' * Common.position
and expr' =
  | Var of Common.variable
  | Type
  | Eq of expr * expr * expr
  | Pi of Common.variable * expr * expr
  | Lambda of Common.variable * expr option * expr
  | App of expr * expr
  | Ascribe of expr * expr

type computation = computation' * Common.position
and computation' =
  | Infer of expr
  | Check of bool * expr * expr
 
(** Toplevel directives. *)
type directive = directive' * Common.position
and directive' =
  | Quit
  | Help
  | Context
  | Parameter of Common.variable * expr
  | Definition of Common.variable * expr
  | Eval of expr
  | Do of computation

