(** Abstract syntax of input files. *)

(** Abstract syntax of terms as given by the user. *)
type term = term' * Common.position
and term' =
  | Var of Common.variable
  | Type
  | Lambda of Common.variable * term option * term
  | Pi of Common.variable * term * term
  | App of term * term
  | Ascribe of term * term
  | Operation of operation_tag * term list
  | Handle of term * handler

and operation_tag =
  | Inhabit

and computation = computation' * Common.position
and computation' =
  | Return of term
  | Let of Common.variable * term * computation

and handler =
   (operation_tag * term list * computation) list

type toplevel = toplevel' * Common.position
and toplevel' =
  | TopDef of Common.variable * term
  | TopParam of Common.variable list * term
  | Context
  | Help
  | Quit

