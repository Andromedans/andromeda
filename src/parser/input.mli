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
  | Hint of expr * comp
  | Inhabit of expr * comp
  | Ascribe of comp * ty
  | Lambda of (Name.t * comp option) list * comp
  | Spine of comp * comp list
  | Prod of (Name.t * ty) list * comp
  | Eq of comp * comp
  | Refl of comp
  | Bracket of comp
  | Inhab

(** Sugared types *)
and ty = term

(** Sugared computations *)
and comp = term

(** Sugared expressions *)
and expr = term

(** Sugared toplevel commands *)
type toplevel = toplevel' * Location.t
and toplevel' =
  | Primitive of Name.t list * (Name.t * bool * ty) list * ty (** introduce a primitive operation, the boolean is [true] if reducing *)
  | TopLet of Name.t * (Name.t * ty) list * ty option * comp (** global let binding *)
  | TopCheck of comp (** infer the type of a computation *)
  | TopBeta of comp (** global beta hint *)
  | TopEta of comp (** global eta hint *)
  | TopHint of comp (** global hint *)
  | TopInhabit of comp (** global inhabit hint *)
  | Verbosity of int
  | Include of string list
  | Quit (** quit the toplevel *)
  | Help (** print help *)
  | Context (** print the current context *)
