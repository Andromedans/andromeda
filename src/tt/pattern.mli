(** Pattern matching support for hints. *)

(** Spine patterns must start with a [name]. *)
type name = Name.t

(** The type of term patterns. *)
type term = private
  | PVar of Syntax.bound
  | Name of name
  | Spine of name * (Tt.ty, Tt.ty) Tt.abstraction * term list
  | Eq of ty * term * term
  | Refl of ty * term
  | Term of Tt.term * Tt.ty

(** The type of type patterns. *)
and ty = Ty of term

(** A pattern is given as an abstraction of a term pattern *)
type t = (Tt.ty, term) Tt.abstraction

(** A beta hint is an abstracted term pattern and a term. We match against
    the pattern and rewrite into the term. *)
type beta_hint = (Tt.ty, term * Tt.term) Tt.abstraction

(** An eta hint is an abstracted term pattern  with a list of universally quantified
    equations. We match against the pattern and check the resulting equations. *)
type eta_hint = (Tt.ty, term * term * ty) Tt.abstraction

(** Wrap a name as a pattern *)
val name : name -> term

val make_beta_hint : loc:Location.t -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction -> beta_hint

val make_eta_hint : loc:Location.t -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction -> eta_hint

val print_pattern : ?max_level:int -> Name.t list -> t -> (Format.formatter -> unit)

val print_beta_hint : ?max_level:int -> Name.t list -> beta_hint -> Format.formatter -> unit

val print_eta_hint : ?max_level:int -> Name.t list -> eta_hint -> Format.formatter -> unit
