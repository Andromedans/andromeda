(** Abstract syntax of value types and terms *)

type term = term' * Location.t
and term' = private
  | Type
  | Name of Name.t (** a free variable *)
  | Bound of Syntax.bound (** a bound variable *)
  | Lambda of (ty, term * ty) abstraction
    (** a lambda abstraction [fun (x1:A1) ... (xn:An) -> e : A] where
        [Ak] depends on [x1, ..., x{k-1}], while [e] and [A] depends on
        [x1, ..., xn] *)
  | Spine of term * (ty, ty) abstraction * term list
  (** a spine [e ((x1 : t1) ..., (xn : tn) : t) e1 ... en] means that
      [e] is applied to [e1, ..., en], and that the type of [e] is
      [forall (x1 : t1) ... (xn : tn), t]. Here [tk] depends on
      [x1, ..., x{k-1}] and [t] depends on [x1, ..., xn]. *)
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
and ('a, 'b) abstraction = (Name.t * 'a) list * 'b

(** Term constructors, the do not check for legality of constructions. *)
val mk_name: loc:Location.t -> Name.t -> term
val mk_bound: loc:Location.t -> Syntax.bound -> term
val mk_lambda: loc:Location.t -> (Name.t * ty) list -> term -> ty -> term
val mk_spine: loc:Location.t -> term -> (Name.t * ty) list -> ty -> term list -> term
val mk_type: loc:Location.t -> term
val mk_type_ty: loc:Location.t -> ty
val mk_prod: loc:Location.t -> (Name.t * ty) list -> ty -> term
val mk_prod_ty: loc:Location.t -> (Name.t * ty) list -> ty -> ty
val mk_eq: loc:Location.t -> ty -> term -> term -> term
val mk_eq_ty: loc:Location.t -> ty -> term -> term -> ty
val mk_refl: loc:Location.t -> ty -> term -> term

(** Coerce a value to a type (does not check whether this is legal). *)
val ty : term -> ty

(** The type Type *)
val typ : ty

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
val unabstract: Name.t list -> int -> term -> term

(** [unabstract_ty [x0,...,x{n-1}] k t] replaces bound variables in [t] indexed by [k, ..., k+n-1]
    with names [x0, ..., x{n-1}]. *)
val unabstract_ty: Name.t list -> int -> ty -> ty

(** [abstract xs k e] replaces names [xs] in term [e] with bound variables [k, ..., k+n-1] where
    [xs] is the list [x0,...,x{n-1}]. *)
val abstract : Name.t list -> int -> term -> term

val abstract_ty : Name.t list -> int -> ty -> ty

(** [shift k e] shifts all bound variables in [e] by [k]. This is used when a term descends into
    an extended environment (so its deBruijn indices are out of sync). *)
val shift : int -> term -> term

val shift_ty : int -> ty -> ty

val occurs: Syntax.bound -> term -> int

val occurs_ty: Syntax.bound -> ty -> int

val occurs_term_ty: Syntax.bound -> term * ty -> int

val occurs_abstraction:
  (Syntax.bound -> 'u -> int) ->
  (Syntax.bound -> 'v -> int) ->
  Syntax.bound -> ('u, 'v) abstraction -> int

val print_ty : ?max_level:int -> Name.t list -> ty -> Format.formatter -> unit
val print_term : ?max_level:int -> Name.t list -> term -> Format.formatter -> unit
