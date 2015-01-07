(** The abstract syntax of input. *)

type term = term' * Location.t
and term' =
  (* expressions *)
  | Var of Common.name
  | Type
  (* computations *)
  | Let of (Common.name * comp) list * comp
  | Ascribe of comp * ty
  | Lambda of (Common.name * ty) list * comp
  | Spine of expr * expr list
  | Prod of (Common.name * ty) list * comp
  | Eq of expr * expr
  | Refl of expr

and ty = term
and comp = term
and expr = term

(** Toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Parameter of Common.name list * ty (** introduce parameters into the context *)
  | TopLet of Common.name * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | Quit
  | Help
  | Context
