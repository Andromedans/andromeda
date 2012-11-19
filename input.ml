(** Abstract syntax of input files. *)

type variable = Common.variable

(** Abstract syntax of universe expressions. *)
type universe = int option

(** Abstract syntax of expressions. *)
type expr = expr' * Common.position
and expr' =
  | Underscore
  | Var of variable
  | Universe of universe
  | Pi of abstraction
  | Lambda of abstraction
  | App of expr * expr
  | Ascribe of expr * expr
 
(** An abstraction [(x,t,e)] indicates that [x] of (optionally given) type [t] is bound in [e]. *)
and abstraction = variable * expr * expr

(** Toplevel directives. *)
type directive = directive' * Common.position
and directive' =
  | Quit
  | Help
  | Context
  | Parameter of variable * expr
  | Definition of variable * expr
  | Check of expr
  | Eval of expr
