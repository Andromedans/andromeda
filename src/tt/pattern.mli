(** Pattern matching support for hints. *)

(** The type of term patterns. *)
type term =
  | PVar of Syntax.bound
  | Spine of term * (term * Tt.ty, Tt.ty) Tt.abstraction
  | Eq of ty * term * term
  | Refl of ty * term
  | Term of Tt.term * Tt.ty

(** The type of type patterns. *)
and ty = Ty of term

(** A pattern is given as an abstraction of a term pattern *)
type t = (Tt.ty, term) Tt.abstraction

type beta_hint = (Tt.ty, term * Tt.term) Tt.abstraction

type eta_hint = unit

(** Given a term [e] of type [t] in abstraction [xts] (that is, the first argument is [(xts, (e,t))]),
    return a list [pvars] and a pattern [p]. The list contains those bound variables which will never
    be matched by [p]. Thus, for the purposes of beta hints the list should be empty, and for eta hints
    it should only contain bound variables whose type is equality. *)
val make : (Tt.ty, Tt.term * Tt.ty) Tt.abstraction -> Syntax.bound list * term

val make_beta_hint : loc:Location.t -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction -> beta_hint

val print_pattern : ?max_level:int -> Name.t list -> t -> (Format.formatter -> unit)

val print_beta_hint : ?max_level:int -> Name.t list -> beta_hint -> Format.formatter -> unit