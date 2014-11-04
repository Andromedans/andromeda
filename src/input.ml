(** The abstract syntax of input. *)

type comp = comp' * Position.t
and comp' =
  | Let of Common.name * comp * comp
  | Term of term

and expr = expr' * Position.t
and expr' =
  | Var of Common.name
  | Type
  | Ascribe of term * ty
  | Lambda of Common.name * ty * term
  | App of term * term
  | Prod of Common.name * ty * ty
  | Eq of term * term
  | Refl of term

and ty = expr

and term = expr

type toplevel = toplevel' * Position.t
and toplevel' =
  | Parameter of Common.name list * ty
  | TopLet of Common.name * comp
  | TopCheck of comp
  | Quit
  | Help
  | Context

let anonymous = "_"
