(** Sugared input syntax

    The abstract syntax of input as typed by the user. At this stage
    there is no distinction between computations, expressions, and types.
    However, we define type aliases for these for better readability.
    There are no de Bruijn indices either. *)

(** Sugared terms *)
type term = term' * Location.t
and term' =
  (* expressions *)
  | Var of Name.t
  | Type
  (* computations *)
  | Let of (Name.t * comp) list * comp
  | Beta of expr * comp
  | Eta of expr * comp
  | Ascribe of comp * ty
  | Lambda of (Name.t * ty) list * comp
  | Spine of expr * expr list
  | Prod of (Name.t * ty) list * comp
  | Eq of expr * expr
  | Refl of expr

(** Sugared types *)
and ty = term

(** Sugared computations *)
and comp = term

(** Sugared expressions *)
and expr = term

(** Sugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Parameter of Name.t list * ty (** introduce parameters into the context *)
  | TopLet of Name.t * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Context (** print the current context *)
