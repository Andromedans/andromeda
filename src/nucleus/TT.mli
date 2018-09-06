(** Abstract syntax of type-theoretic types and terms *)

type bound

(** The type of TT terms.

    We use locally nameless syntax: names for free variables and deBruijn
    indices for bound variables.
*)

type term = private
  (** a free variable *)
  | Atom of Name.atom

  (** a bound variable *)
  | Bound of bound

  (** a term constructor *)
  | TermConstructor of Name.constant * argument list

  (** a term conversion *)
  | TermConvert of term * Assumption.t * ty


(** The type of TT types. *)
and ty = private

(** the universe *)
  (** a type constructor *)
  | TypeConstructor of Name.constant * argument list

(** an argument of a term or type constructor *)
and argument = private
  | ArgIsTerm of term abstraction
  | ArgIsType of ty abstraction
  | ArgEqType of Assumption.t abstraction
  | ArgEqTerm of Assumption.t abstraction

and 'a abstraction = private
  | Abstract of Name.ident * Assumption.t * 'a abstraction
  | NotAbstract of 'a

(** Term constructors, these do not check for legality of constructions. *)
val mk_atom: Name.atom -> term

(** Create a fully applied type constructor *)
val mk_type_constructor : Name.constant -> argument list -> ty

val mk_arg_is_type : ty abstraction -> argument
val mk_arg_is_term : term abstraction -> argument
val mk_arg_eq_type : Assumption.t abstraction -> argument
val mk_arg_eq_term : Assumption.t abstraction -> argument

(** Make a non-abstracted constructor argument *)
val mk_not_abstract : 'a -> 'a abstraction

(** Abstract a term argument *)
val mk_abstract : (lvl:int -> 'a -> 'a) -> Name.atom -> ty -> 'a abstraction -> 'a abstraction

(** [instantiate_term e0 k e] replaces bound variable [k] with term [e0] in term [e]. *)
val instantiate_term: term -> lvl:int -> term -> term

(** [instantiate_term e0 k t] replaces bound variable [k] with term [e0] in type [t]. *)
val instantiate_type: term -> lvl:int -> ty -> ty

(** [unabstract_term x0 k e] replaces bound variable [k] in [e] with name [x0]. *)
val unabstract_term: Name.atom -> lvl:int -> term -> term

(** [unabstract_ty x0 k t] replaces bound variable [k] in [t] with name [x0]. *)
val unabstract_type: Name.atom -> lvl:int -> ty -> ty

(** [abstract_term x0 k e] replaces name [x0] in term [e] with bound variable [k] (default [0]) where. *)
val abstract_term : Name.atom -> lvl:int -> term -> term

(** [abstract_term x0 k t] replaces name [x0] in type [t] with bound variable [k] (default [0]) where. *)
val abstract_type : Name.atom -> lvl:int -> ty -> ty

(** abstract followed by instantiate *)
val substitute_term : Name.atom -> term -> term -> term

val substitute_type : Name.atom -> term -> ty -> ty

(** The asssumptions used by a term. *)
val assumptions_term : term -> Assumption.t

(** The assumptions used by a type. *)
val assumptions_type : ty -> Assumption.t

(** [alpha_equal e1 e2] returns [true] if term [e1] and [e2] are alpha equal. *)
val alpha_equal: term -> term -> bool

(** [alpha_equal_ty t1 t2] returns [true] if types [t1] and [t2] are alpha equal. *)
val alpha_equal_ty: ty -> ty -> bool

type print_env =
  { forbidden : Name.ident list ;
    atoms : Name.atom_printer ; }

val print_type : ?max_level:Level.t -> penv:print_env -> ty -> Format.formatter -> unit
val print_term : ?max_level:Level.t -> penv:print_env -> term -> Format.formatter -> unit

module Json :
sig

  (** Convert a term to JSON *)
  val term : term -> Json.t

  (** Convert a type to JSON *)
  val ty : ty -> Json.t

end
