(** Abstract syntax of input files. *)

(** Abstract syntax of expressions as given by the user. *)
type expr = expr' * Common.position
and expr' =
  | Var of Common.variable
  | Universe of int
  | Pi of Common.variable * expr * expr
  | Lambda of Common.variable * expr
  | App of expr * expr
  | Ascribe of expr * expr
 
(** Toplevel directives. *)
type directive = directive' * Common.position
and directive' =
  | Quit
  | Help
  | Context
  | Parameter of Common.variable * expr
  | Definition of Common.variable * expr
  | Check of expr
  | Eval of expr
