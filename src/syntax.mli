(** Abstract syntax of computations and expressions. *)

(** Bound variables *)
type bound = int

type expr = expr' * Location.t
 and expr' =
   | Name of Name.t
   | Bound of bound
   | Meta of bound
   | Type

and ty = expr

and comp = comp' * Location.t
and comp' = 
  | Return of expr
  | Let of (Name.t * comp) list * comp
  | Ascribe of comp * ty
  | Lambda of (Name.t * ty) list * comp
  | Spine of expr * expr list
  | Prod of (Name.t * ty) list * comp
  | Eq of expr * comp
  | Refl of expr

type toplevel = toplevel' * Location.t
and toplevel' =
  | Parameter of Name.t list * comp (** introduce parameters into the context *)
  | TopLet of Name.t * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | Quit
  | Help
  | Context
