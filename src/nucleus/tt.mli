(** Abstract syntax of value types and terms *)

type ('a,'b) constrain =
  | Unconstrained of 'a
  | Constrained of 'b

(** An [('a, 'b) abstraction] is a ['b] bound by (x, 'a) *)
type ('a, 'b) abstraction = (Name.ident * 'a) * 'b

type bound = int

(** The type of TT terms.
    (For details on the mutual definition with [term'], see module Location.)

    We use locally nameless syntax: names for free variables and deBruijn
    indices for bound variables. In terms of type [term], bound variables are
    not allowed to appear "bare", i.e., without an associated binder.
*)
type term = { term : term' ; assumptions : Assumption.t; loc : Location.t}
and term' = private
  (** term denoting the type of types *)
  | Type

  (** a free variable *)
  | Atom of Name.atom

  (** a bound variable *)
  | Bound of bound

  (** a constant *)
  | Constant of Name.constant

  (** a lambda abstraction [fun (x1 : t1) -> e : t] *)
  | Lambda of (term * ty) ty_abstraction

  (** an application tagged with the type at wich it happens *)
  | Apply of term * ty ty_abstraction * term

  (** a dependent product [forall (x1 : t1), t] *)
  | Prod of ty ty_abstraction

  (** strict equality type [e1 == e2] where [e1] and [e2] have type [t]. *)
  | Eq of ty * term * term

  (** reflexivity [refl e] where [e] has type [t]. *)
  | Refl of ty * term

  (** signature, also known as structure type *)
  | Signature of signature

  (** structure, also known as record or module *)
  | Structure of structure

  (** a projection [e s .li] means that we project field [li] of [e]
      where [e] has type [Signature s].
      [li] must not be a constrained field of [s]. *)
  | Projection of term * signature * Name.label

(** Since we have [Type : Type] we do not distinguish terms from types,
    so the type of type [ty] is just a synonym for the type of terms.
    However, we tag types with the [Ty] constructor to avoid nasty bugs. *)
and ty = private
    | Ty of term

(** A ['a ty_abstraction] is a n abstraction where the [a1, ..., an] are types *)
and 'a ty_abstraction = (ty, 'a) abstraction

and sig_def = (Name.label * Name.ident * ty) list

(** A signature with sharing constraints [s with li = vi], the [li] are implicit.
    [vi] is [Unconstrained xi] when [li] has no constraint, then [xi] is bound in future constraints,
            [Constrained ei] when it has one.
*)
and signature = Name.signature * (Name.ident, term) constrain list

(** A structure [s,es] where [es] are the values of the non constrained fields of [s].
    The [es] do not bind labels. *)
and structure = signature * term list

(** Term constructors, these do not check for legality of constructions. *)
val mk_atom: loc:Location.t -> Name.atom -> term
val mk_constant: loc:Location.t -> Name.ident -> term
val mk_lambda: loc:Location.t -> Name.ident -> ty -> term -> ty -> term
val mk_apply: loc:Location.t -> term -> Name.ident -> ty -> ty -> term -> term
val mk_type: loc:Location.t -> term
val mk_type_ty: loc:Location.t -> ty
val mk_prod: loc:Location.t -> Name.ident -> ty -> ty -> term
val mk_prod_ty: loc:Location.t -> Name.ident -> ty -> ty -> ty
val mk_eq: loc:Location.t -> ty -> term -> term -> term
val mk_eq_ty: loc:Location.t -> ty -> term -> term -> ty
val mk_refl: loc:Location.t -> ty -> term -> term
val mk_signature : loc:Location.t -> signature -> term
val mk_signature_ty : loc:Location.t -> signature -> ty
val mk_structure : loc:Location.t -> signature -> term list -> term
val mk_projection : loc:Location.t -> term -> signature -> Name.ident -> term

(** Coerce a value to a type (does not check whether this is legal). *)
val ty : term -> ty

(** The type Type *)
val typ : ty

(** Add the given set of atoms as assumption to a term. *)
val mention_atoms : Name.AtomSet.t -> term -> term

(** Add an assumption to a term. *)
val mention : Assumption.t -> term -> term

(** [instantiate [e0,...,e{n-1}] k e] replaces bound variables indexed by [k, ..., k+n-1]
    with terms [e0, ..., e{n-1}]. *)
val instantiate: term list -> ?lvl:int -> term -> term

val instantiate_ty: term list -> ?lvl:int -> ty -> ty

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

(** abstract followed by instantiate *)
val substitute : Name.atom list -> term list -> term -> term

val substitute_ty : Name.atom list -> term list -> ty -> ty


val occurs: bound -> term -> int

val occurs_ty: bound -> ty -> int

val occurs_term_ty: bound -> term * ty -> int

val occurs_ty_abstraction:
  (bound -> 'a -> int) ->
  bound -> 'a ty_abstraction -> int

(** The asssumptions used by a term. *)
val assumptions_term : term -> Name.AtomSet.t

(** The assumptions used by a type. *)
val assumptions_ty : ty -> Name.AtomSet.t

(** Structure stuff *)

type struct_field =
  | Shared of term
  | Explicit of term

(** Return the list of terms defining the structure, with constraints fully instantiated. *)
val struct_combine : loc:Location.t -> structure -> struct_field list

(** Makes the projection, even when the field is constrained. *)
val field_value : loc:Location.t -> sig_def -> structure -> Name.label -> term

(** [field_type s s_def e p] where [e : Signature s] and [s_def] is the definition
    of [s] computes the value and type of [e.p], taking it from the constraints if possible. *)
val field_project : loc:Location.t -> sig_def -> signature -> term -> Name.label -> term*ty

(** [alpha_equal e1 e2] returns [true] if term [e1] and [e2] are alpha equal. *)
val alpha_equal: term -> term -> bool

(** [alpha_equal_ty t1 t2] returns [true] if types [t1] and [t2] are alpha equal. *)
val alpha_equal_ty: ty -> ty -> bool

val alpha_equal_sig : signature -> signature -> bool

type print_env =
  { forbidden : Name.ident list ;
    atoms : Name.atom_printer ;
    sigs : Name.signature -> Name.label list }

val print_ty : ?max_level:Level.t -> penv:print_env -> ty -> Format.formatter -> unit
val print_term : ?max_level:Level.t -> penv:print_env -> term -> Format.formatter -> unit
val print_sig_def : penv:print_env -> sig_def -> Format.formatter -> unit

