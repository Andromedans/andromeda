(** Abstract syntax of types and terms. *)

type term = term' * Location.t
and term' = private
  | Type
  | Name of Common.name (** a free variable *)
  | Bound of Common.bound (** a bound variable *)
  | Lambda of (ty, term * ty) abstraction
    (** a lambda abstraction [fun (x1:A1) ... (xn:An) -> e : A] where
        [Ak] depends on [x1, ..., x{k-1}], while [e] and [A] depends on
        [x1, ..., xn] *)
  | Spine of term * (term * ty, ty) abstraction
    (** a spine [e [(x1,(e1,A1)); ..., (xn,(en,An))] : A] means that
        [e] is applied to [e1, ..., en], and that the type of [e] has type
        [forall (x1:A1) ... (xn:An), A]. Here again [Ak] depends on
        [x1, ..., x{k-1}] and [A] depends on [x1, ..., xn]. *)
  | Prod of (ty, ty) abstraction
    (** dependent product [forall (x1:A1) ... (xn:An), A], where [Ak] depends on
        [x1, ..., x{k-1}] and [A] depends on [x1, ..., xn]. *)
  | Eq of ty * term * term
    (** strict equality type [e1 == e2] where [e1] and [e2] have type [A]. *)
  | Refl of ty * term (** reflexivity [refl e] where [e] has type [A]. *)

(** Since we have [Type : Type] we do not distinguish terms from types,
    so the type of type [ty] is just a synonym for the type of terms. 
    However, we tag types with the [Ty] constructor to avoid nasty bugs. *)
and ty = private
    | Ty of term

(** An [(A,B) abstraction] is a [B] bound by [x1:a1, ..., xn:an] where
    the [a1, ..., an] have type [A]. *)
and ('a, 'b) abstraction = (Common.name * 'a) list * 'b

(** A value is the result of a computation. *)
type value = term * ty

(** A result of computation *)
type result =
  | Return of value

(** Term constructors, the do not check for legality of constructions. *)
val mk_name: loc:Location.t -> Common.name -> term
val mk_bound: loc:Location.t -> Common.bound -> term
val mk_lambda: loc:Location.t -> (Common.name * ty) list -> term -> ty -> term
val mk_spine: loc:Location.t -> term -> (Common.name * (term * ty)) list -> ty -> term
val mk_type: loc:Location.t -> term
val mk_type_ty: loc:Location.t -> ty
val mk_prod: loc:Location.t -> (Common.name * ty) list -> ty -> term
val mk_prod_ty: loc:Location.t -> (Common.name * ty) list -> ty -> ty
val mk_eq: loc:Location.t -> ty -> term -> term -> term
val mk_eq_ty: loc:Location.t -> ty -> term -> term -> ty
val mk_refl: loc:Location.t -> ty -> term -> term

(** Coerce a value to a type (does not check whether this is legal). *)
val ty : term -> ty

(** The type Type *)
val typ : ty

(** Alpha equality of terms *)
val equal : term -> term -> bool

(** Alpha equality of types *)
val equal_ty : ty -> ty -> bool

(** [instantiate [e0,...,e{n-1}] k e] replaces bound variables indexed by [k, ..., k+n-1]
    with terms [e0, ..., e{n-1}]. *)
val instantiate: term list -> int -> term -> term

val instantiate_abstraction: 
  (term list -> int -> 'u -> 'u) ->
  (term list -> int -> 'v -> 'v) ->
  term list ->
  int ->
  ('u, 'v) abstraction -> ('u, 'v) abstraction

val instantiate_ty: term list -> int -> ty -> ty

val instantiate_term_ty: term list -> int -> term * ty -> term * ty

(** [unabstract [x0,...,x{n-1}] k e] replaces bound variables in [e] indexed by [k, ..., k+n-1]
    with names [x0, ..., x{n-1}]. *)
val unabstract: Common.name list -> int -> term -> term

(** [unabstract_ty [x0,...,x{n-1}] k t] replaces bound variables in [t] indexed by [k, ..., k+n-1]
    names [x0, ..., x{n-1}]. *)
val unabstract_ty: Common.name list -> int -> ty -> ty

val abstract : Common.name list -> int -> term -> term

val abstract_ty : Common.name list -> int -> ty -> ty

(* Does de Bruijn index 0 get used in the given term? *)
val occurs : term -> bool

(** Does de Bruijn index 0 get used in the given type? *)
val occurs_ty : ty -> bool

val print_ty : ?max_level:int -> ty -> Format.formatter -> unit

val print_value : ?max_level:int -> value -> Format.formatter -> unit
