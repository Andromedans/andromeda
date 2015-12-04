(** Abstract syntax of value types and terms *)

(** An [('a, 'b) abstraction] is a ['b] bound by [(x1, 'a1), ..., (xn, 'an)]. *)
type ('a, 'b) abstraction = (Name.ident * 'a) list * 'b

type term = { term : term' ; assumptions : Assumption.t; loc : Location.t}
and term' = private
(** The type of TT terms.
    (For details on the mutual definition with [term'], see module Location.)

    We use locally nameless syntax: names for free variables and deBruijn
    indices for bound variables. In terms of type [term], bound variables are
    not allowed to appear "bare", i.e., without an associated binder.

    Instead of nesting binary applications [((e1 e2) ... en)], we use
    spines [e1 [e2; ...; en]]. The reason for this is one of efficiency:
    because we need to tag every application with the argument and result type,
    nested applications use quadratic space (in the number of the applications)
    whereas spines use linear space. Consequently, lambda abstractions and
    products also accept lists of arguments.

    To represent nested bindings, we use an auxiliary type
    [(A, B) abstraction], which consists of a list [(x1 : a1), ..., (xn : an)],
    where each [ak] has type [A] and can depend on variables [x1, ..., x{k-1}],
    and of a single [b] of type [B] that can depend on all [x1, ..., xn]. *)


  (** term denoting the type of types *)
  | Type

  (** a free variable *)
  | Atom of Name.atom

  (** a bound variable *)
  | Bound of Syntax.bound

  (** a constant *)
  | Constant of Name.ident * term list

  (** a lambda abstraction [fun (x1 : t1) ... (xn : tn) -> e : t] where
      [tk] depends on [x1, ..., x{k-1}], while [e] and [t] depend on
      [x1, ..., xn] *)
  | Lambda of (term * ty) ty_abstraction

  (** a spine [e ((x1 : t1) ..., (xn : tn) : t) e1 ... en] means that
      [e] is applied to [e1, ..., en], and that the type of [e] is
      [forall (x1 : t1) ... (xn : tn), t]. Here [tk] depends on
      [x1, ..., x{k-1}] and [t] depends on [x1, ..., xn]. *)
  | Spine of term * ty ty_abstraction * term list

  (** a dependent product [forall (x1 : t1) ... (xn : tn), t], where [tk]
      depends on [x1, ..., x{k-1}] and [t] depends on [x1, ..., xn]. *)
  | Prod of ty ty_abstraction

  (** strict equality type [e1 == e2] where [e1] and [e2] have type [t]. *)
  | Eq of ty * term * term

  (** reflexivity [refl e] where [e] has type [t]. *)
  | Refl of ty * term

  (** the inhabitant of a bracket type *)
  | Inhab of ty

  (** bracket type *)
  | Bracket of ty

  (** signature, also known as structure type *)
  | Signature of signature

  (** structure, also known as record or module *)
  | Structure of structure

  (** a projection [e {x1:t1, ..., xn:tn} .xi] means that we project field [xi] of [e] and [e] has type [{x1:t1, ..., xn:tn}].
      Currently field types do not depend on other fields so the result has type [ti]. *)
  | Projection of term * signature * Name.ident

(** Since we have [Type : Type] we do not distinguish terms from types,
    so the type of type [ty] is just a synonym for the type of terms.
    However, we tag types with the [Ty] constructor to avoid nasty bugs. *)
and ty = private
    | Ty of term

(** A ['a ty_abstraction] is a n abstraction where the [a1, ..., an] are types *)
and 'a ty_abstraction = (ty, 'a) abstraction

and signature = (Name.ident * Name.ident * ty) list

and structure = (Name.ident * Name.ident * ty * term) list

(** The signature of a constant. The booleans indicate whether the arguments
    should be eagerly reduced. *)
type constsig = ((bool * ty), ty) abstraction

(** Term constructors, the do not check for legality of constructions. *)
val mk_atom: loc:Location.t -> Name.atom -> term
val mk_constant: loc:Location.t -> Name.ident -> term list -> term
val mk_lambda: loc:Location.t -> (Name.ident * ty) list -> term -> ty -> term
val mk_spine: loc:Location.t -> term -> (Name.ident * ty) list -> ty -> term list -> term
val mk_type: loc:Location.t -> term
val mk_type_ty: loc:Location.t -> ty
val mk_prod: loc:Location.t -> (Name.ident * ty) list -> ty -> term
val mk_prod_ty: loc:Location.t -> (Name.ident * ty) list -> ty -> ty
val mk_eq: loc:Location.t -> ty -> term -> term -> term
val mk_eq_ty: loc:Location.t -> ty -> term -> term -> ty
val mk_refl: loc:Location.t -> ty -> term -> term
val mk_bracket: loc:Location.t -> ty -> term
val mk_bracket_ty: loc:Location.t -> ty -> ty
val mk_inhab: loc:Location.t -> ty -> term
val mk_signature : loc:Location.t -> signature -> term
val mk_signature_ty : loc:Location.t -> signature -> ty
val mk_structure : loc:Location.t -> structure -> term
val mk_projection : loc:Location.t -> term -> signature -> Name.ident -> term

(** Coerce a value to a type (does not check whether this is legal). *)
val ty : term -> ty

(** The type Type *)
val typ : ty

val mention : Assumption.t -> term -> term

(** [instantiate [e0,...,e{n-1}] k e] replaces bound variables indexed by [k, ..., k+n-1]
    with terms [e0, ..., e{n-1}]. *)
val instantiate: term list -> ?lvl:int -> term -> term

val instantiate_ty_abstraction:
  (term list -> ?lvl:int -> 'a -> 'a) ->
  term list -> ?lvl:int -> 'a ty_abstraction -> 'a ty_abstraction

val instantiate_ty: term list -> ?lvl:int -> ty -> ty

val instantiate_term_ty: term list -> ?lvl:int -> term * ty -> term * ty

(** [unabstract [x0,...,x{n-1}] k e] replaces bound variables in [e] indexed by [k, ..., k+n-1]
    with names [x0, ..., x{n-1}]. *)
val unabstract: Name.atom list -> ?lvl:int -> term -> term

(** [unabstract_ty [x0,...,x{n-1}] k t] replaces bound variables in [t] indexed by [k, ..., k+n-1]
    with names [x0, ..., x{n-1}]. *)
val unabstract_ty: Name.atom list -> ?lvl:int -> ty -> ty

(** [abstract xs k e] replaces names [xs] in term [e] with bound variables [k, ..., k+n-1] where
    [xs] is the list [x0,...,x{n-1}]. *)
val abstract : Name.atom list -> ?lvl:int -> term -> term

val abstract_ty : Name.atom list -> ?lvl:int -> ty -> ty

val abstract_ty_abstraction :
  (Name.atom list -> ?lvl:int -> 'a -> 'a) ->
  Name.atom list -> ?lvl:int -> 'a ty_abstraction -> 'a ty_abstraction

val occurs: Syntax.bound -> term -> int

val occurs_ty: Syntax.bound -> ty -> int

val occurs_term_ty: Syntax.bound -> term * ty -> int

val occurs_ty_abstraction:
  (Syntax.bound -> 'a -> int) ->
  Syntax.bound -> 'a ty_abstraction -> int


val gather_assumptions : term -> Assumption.t

val gather_assumptions_ty : ty -> Assumption.t

(** Module stuff *)

(** [field_value defs p] is [defs.p] with all bound variables instantiated appropriately. *)
val field_value : loc:Location.t -> structure -> Name.ident -> term

(** [field_type tys e p] when [e : {tys}] is the type of [e.p] *)
val field_type : loc:Location.t -> signature -> term -> Name.ident -> ty

(** [alpha_equal e1 e2] returns [true] if term [e1] and [e2] are alpha equal. *)
val alpha_equal: term -> term -> bool

(** [alpha_equal_ty t1 t2] returns [true] if types [t1] and [t2] are alpha equal. *)
val alpha_equal_ty: ty -> ty -> bool

val print_ty : ?max_level:int -> Name.ident list -> ty -> Format.formatter -> unit
val print_term : ?max_level:int -> Name.ident list -> term -> Format.formatter -> unit
val print_constsig : ?max_level:int -> Name.ident list -> constsig -> Format.formatter -> unit
