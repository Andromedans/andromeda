(** Desugared input syntax *)

(** Bound variables - represented by de Bruijn indices *)
type bound = int

(** Desugared expressions *)
type expr = expr' * Location.t
and expr' =
  | Name of Name.t
  | Bound of bound
  | Type

(** Desugared types - indistinguishable from expressions  *)
and ty = expr

(** Desugared computations *)
and comp = comp' * Location.t
and comp' =
  | Return of expr
  | Let of (Name.t * comp) list * comp
  | Ascribe of comp * ty
  | Lambda of (Name.t * ty) list * comp
  | Spine of expr * comp list (* spine arguments are computations because we want
                                 to evaluate in checking mode, once we know their types. *)
  | Prod of (Name.t * ty) list * comp
  | Eq of expr * comp
  | Refl of expr

(** Desugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Parameter of Name.t list * comp (** introduce parameters into the context *)
  | TopLet of Name.t * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Context (** print the current context *)
