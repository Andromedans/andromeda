(** The abstract syntax of input. *)

type term = term' * Location.t
and term' =
  (* expressions *)
  | Var of Name.t
  | Type
  (* computations *)
  | Let of (Name.t * comp) list * comp
  | Ascribe of comp * ty
  | Lambda of (Name.t * ty) list * comp
  | Spine of expr * expr list
  | Prod of (Name.t * ty) list * comp
  | Eq of expr * expr
  | Refl of expr

and ty = term
and comp = term
and expr = term

(** Toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Parameter of Name.t list * ty (** introduce parameters into the context *)
  | TopLet of Name.t * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | Quit
  | Help
  | Context
