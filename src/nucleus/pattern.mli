(** Pattern matching support for hints. *)

(** A type which is exactly like [Tt.ty] except that its bound
    variables refer to pattern variables instead of the ordinary
    bound variables. *)
type pty = Tt.ty

type pterm = Tt.term

type 'a pabstraction = (Name.ident * pty) list * 'a

(** The type of term patterns. *)
type term =
  | PVar of Syntax.bound
  | Atom of Name.atom
  | Constant of Name.ident * term list
  | Spine of term * pty pabstraction * term list
  | Bracket of ty
  | Eq of ty * term * term
  | Refl of ty * term
  | Term of pterm * pty

(** The type of type patterns. *)
and ty = Ty of term

(** A pattern is given as an abstraction of a term pattern *)
type t = term pabstraction

(** A beta hint is an abstracted term pattern and a term. We match against
    the pattern and rewrite into the term. *)
type beta_pattern =
  | BetaAtom of Name.atom
  | BetaConstant of Name.ident * term list
  | BetaSpine of term * pty pabstraction * term list

type beta_hint = Context.t * (beta_pattern * Tt.term) pabstraction

(** An eta hint is an abstracted type pattern together with variables that match
    the lhs and rhs of an equation. *)
type eta_hint = Context.t * (ty * Syntax.bound * Syntax.bound) pabstraction

(** A general hint is an abstracted triple of patterns that match the type and both
    sides of equation. *)
type general_hint = Context.t * (ty * term * term) pabstraction

(** An inhabit hint is a universally quantified type. *)
type inhabit_hint = Context.t * ty pabstraction

(** To each pattern and whnf term we associate a hint key in such a way that
    a pattern and a term match only if their hint keys are equal. This way we
    can look up possibly matching hints by hint keys.

    There is no key for spines because the key for a spine is the key of its
    head. *)
type hint_key =
  | Key_Type
  | Key_Constant of Name.ident
  | Key_Atom of Name.atom
  | Key_Lambda
  | Key_Prod
  | Key_Eq
  | Key_Refl
  | Key_Inhab
  | Key_Bracket

type general_key = hint_key option * hint_key option * hint_key option

(* Compute the hint key of a term, fail on De Bruijn index. *)
val term_key : Tt.term -> hint_key

val term_key_opt : Tt.term -> hint_key option

(* Compute the hint key of a type, fail on De Bruijn index. *)
val ty_key : Tt.ty -> hint_key

val ty_key_opt : Tt.ty -> hint_key option

(* Compute the hint key of a general hint. When we find a pvar in a key
   position, return None. *)
val general_key : Tt.term -> Tt.term -> Tt.ty -> general_key

val print_pattern : ?max_level:int -> Name.ident list -> t -> (Format.formatter -> unit)

val print_beta_hint : ?max_level:int -> Name.ident list -> beta_hint -> Format.formatter -> unit

val print_eta_hint : ?max_level:int -> Name.ident list -> eta_hint -> Format.formatter -> unit

val print_inhabit_hint : ?max_level:int -> Name.ident list -> inhabit_hint -> Format.formatter -> unit

val print_hint : ?max_level:int -> Name.ident list -> general_hint -> Format.formatter -> unit

val print_key : ?max_level:int -> hint_key -> Format.formatter -> unit

val print_general_key : ?max_level:int -> general_key -> Format.formatter -> unit
