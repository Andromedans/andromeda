(** Abstract syntax of type-theoretic types and terms *)

type bound

(** We use locally nameless syntax: names for free variables and deBruijn
   indices for bound variables. *)

(** An abstracted entity. *)
type ('a, 'b) abstraction = private
  | Abstract of Name.ident * 'a * ('a,'b) abstraction
  | NotAbstract of 'b

(** An abstracted argument of a constructor (does not carry any type information). *)
type 'a argument_abstraction = (unit, 'a) abstraction

type term = private
  (** a free variable *)
  | TermAtom of Name.atom * ty

  (** a bound variable *)
  | TermBound of bound

  (** a term constructor *)
  | TermConstructor of Name.constant * argument list

  (** a term conversion *)
  | TermConvert of term * assumption * ty

(** The type of TT types. *)
and ty = private
  (** a type constructor *)
  | TypeConstructor of Name.constant * argument list

and eq_type = private EqType of assumption * ty * ty

and eq_term = private EqTerm of assumption * term * term * ty

and assumption = ty Assumption.t

(** An argument of a term or type constructor. *)
and argument = private
  | ArgIsTerm of term argument_abstraction
  | ArgIsType of ty argument_abstraction
  | ArgEqType of assumption argument_abstraction
  | ArgEqTerm of assumption argument_abstraction

(** Term constructors, these do not check for legality of constructions. *)

(** Create an atom of the given type. *)
val mk_atom : Name.atom -> ty -> term

(** Create an atom of the given type, with a fresh name. *)
val fresh_atom : Name.ident -> ty -> term

(** Create a fully applied type constructor *)
val mk_type_constructor : Name.constant -> argument list -> ty

val mk_arg_is_type : ty argument_abstraction -> argument
val mk_arg_is_term : term argument_abstraction -> argument
val mk_arg_eq_type : eq_type argument_abstraction -> argument
val mk_arg_eq_term : eq_term argument_abstraction -> argument

(** Make a non-abstracted constructor argument *)
val mk_not_abstract : 'b -> ('a, 'b) abstraction

(** Abstract a term argument *)
val mk_abstract : Name.ident -> 'a -> ('a, 'b) abstraction -> ('a, 'b) abstraction

(** [instantiate_term e0 ~lvl:k e] replaces bound variable [k] (defualt [0])  with term [e0] in term [e]. *)
val instantiate_term: term -> ?lvl:bound -> term -> term

(** [instantiate_term e0 ~lvl:k t] replaces bound variable [k] (default [0]) with term [e0] in type [t]. *)
val instantiate_type: term -> ?lvl:bound -> ty -> ty

(** [instantiate_abstraction inst_u inst_v e0 ~lvl:k abstr] instantiates bound variable
    [k] (default [0]) with term [e0] in the given abstraction. *)
val instantiate_abstraction :
  (term -> ?lvl:bound -> 'a -> 'a) ->
  (term -> ?lvl:bound -> 'b -> 'b) ->
  term -> ?lvl:bound -> ('a, 'b) abstraction -> ('a, 'b) abstraction

(** [abstract_term x0 ~lvl:k e] replaces atom [x0] in term [e] with bound variable [k] (default [0]). *)
val abstract_term : Name.atom -> ?lvl:bound -> term -> term

(** [abstract_term x0 ~lvl:k t] replaces atom [x0] in type [t] with bound variable [k] (default [0]). *)
val abstract_type : Name.atom -> ?lvl:bound -> ty -> ty

(** abstract followed by instantiate *)
val substitute_term : Name.atom -> term -> term -> term

val substitute_type : Name.atom -> term -> ty -> ty

(** The asssumptions used by a term. *)
val assumptions_term : lvl:bound -> term -> assumption

(** The assumptions used by a type. *)
val assumptions_type : lvl:bound -> ty -> assumption

(** [alpha_equal e1 e2] returns [true] if term [e1] and [e2] are alpha equal. *)
val alpha_equal: term -> term -> bool

(** [alpha_equal_ty t1 t2] returns [true] if types [t1] and [t2] are alpha equal. *)
val alpha_equal_ty: ty -> ty -> bool

val occurs_term : bound -> term -> bool

val occurs_type : bound -> ty -> bool

val occurs_eq_type : bound -> eq_type -> bool

val occurs_eq_term : bound -> eq_term -> bool

type print_env = private
  { forbidden : Name.ident list ;
    atoms : Name.atom_printer ; }

(** Forbid the given identifier from being used as a bound variable. *)
val add_forbidden : Name.ident -> print_env -> print_env

val print_abstraction :
   (bound -> 'a -> bool) ->
   (penv:print_env -> Name.ident * 'a -> Format.formatter -> unit) ->
   (bound -> 'b -> bool) ->
   (?max_level:Level.t -> penv:print_env -> 'b -> Format.formatter -> unit) ->
   ?max_level:Level.t ->
   penv:print_env ->
   ('a, 'b) abstraction ->
   Format.formatter -> unit

val print_type : ?max_level:Level.t -> penv:print_env -> ty -> Format.formatter -> unit

val print_term : ?max_level:Level.t -> penv:print_env -> term -> Format.formatter -> unit

module Json :
sig

  (** Convert a term to JSON *)
  val term : term -> Json.t

  (** Convert a type to JSON *)
  val ty : ty -> Json.t

end
