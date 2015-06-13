(** Pattern matching support for hints. *)

(** A type which is exactly like [Tt.ty] except that its bound
    variables refer to pattern variables instead of the ordinary
    bound variables. *)
type pty = Tt.ty

type pterm = Tt.term

(** The type of term patterns. *)
type term = private
  | PVar of Syntax.bound
  | Name of Name.t
  | Spine of spine_pattern
  | Bracket of ty
  | Eq of ty * term * term
  | Refl of ty * term
  | Term of pterm * pty

(** The type of type patterns. *)
and ty = Ty of term

and spine_pattern = term * (pty, pty) Tt.abstraction * term list

(** A pattern is given as an abstraction of a term pattern *)
type t = (Tt.ty, term) Tt.abstraction

(** A beta hint is an abstracted term pattern and a term. We match against
    the pattern and rewrite into the term. *)
type beta_hint = Name.t * (Tt.ty, spine_pattern * Tt.term) Tt.abstraction

(** An eta hint is an abstracted type pattern together with variables that match
    the lhs and rhs of an equation. *)
type eta_hint = Name.t * (Tt.ty, ty * Syntax.bound * Syntax.bound) Tt.abstraction

(** A general hint is an abstracted triple of patterns that match the type and both
    sides of equation. *)
type hint = Name.t * (Tt.ty, ty * term * term) Tt.abstraction

(** An inhabit hint is a universally quantified type. *)
type inhabit = (Tt.ty, ty) Tt.abstraction

(** Wrap a name as a pattern *)
val make_beta_hint : loc:Location.t -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction -> beta_hint

val make_eta_hint : loc:Location.t -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction -> eta_hint

val make_hint : loc:Location.t -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction -> hint

val make_inhabit : loc:Location.t -> (Tt.ty, Tt.ty) Tt.abstraction -> inhabit

val print_pattern : ?max_level:int -> Name.t list -> t -> (Format.formatter -> unit)

val print_beta_hint : ?max_level:int -> Name.t list -> beta_hint -> Format.formatter -> unit

val print_eta_hint : ?max_level:int -> Name.t list -> eta_hint -> Format.formatter -> unit

val print_inhabit_hint : ?max_level:int -> Name.t list -> inhabit -> Format.formatter -> unit

val print_hint : ?max_level:int -> Name.t list -> hint -> Format.formatter -> unit

