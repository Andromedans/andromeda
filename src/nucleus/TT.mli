(** Abstract syntax of type-theoretic types and terms *)

type bound

(** We use locally nameless syntax: names for free variables and deBruijn
   indices for bound variables. *)

(** The type of TT types. *)
type ty = private
  (** a type constructor *)
  | TypeConstructor of Name.constant * argument list

and term = private
  (** a free variable *)
  | TermAtom of ty atom

  (** a bound variable *)
  | TermBound of bound

  (** a term constructor *)
  | TermConstructor of Name.constant * argument list

  (** a term conversion *)
  | TermConvert of term * assumption * ty

and eq_type = private EqType of assumption * ty * ty

and eq_term = private EqTerm of assumption * term * term * ty

and assumption = ty Assumption.t

and 't atom = private { atom_name : Name.atom ; atom_type : 't }

(** An argument of a term or type constructor. *)
and argument = private
  | ArgIsTerm of term abstraction
  | ArgIsType of ty abstraction
  | ArgEqType of eq_type abstraction
  | ArgEqTerm of eq_term abstraction

(** An abstracted entity. *)
and 'a abstraction = private
  | Abstract of Name.ident * ty * 'a abstraction
  | NotAbstract of 'a


(** Term constructors, these do not check for legality of constructions. *)

(** Create a fresh atom of the given type. *)
val fresh_atom : Name.ident -> 't -> 't atom

(** Create the judgement that an atom has its type. *)
val mk_atom : ty atom -> term

(** Create a fully applied type constructor *)
val mk_type_constructor : Name.constructor -> argument list -> ty

(** Create a fully applied term constructor *)
val mk_term_constructor : Name.constructor -> argument list -> term

val mk_arg_is_type : ty abstraction -> argument
val mk_arg_is_term : term abstraction -> argument
val mk_arg_eq_type : eq_type abstraction -> argument
val mk_arg_eq_term : eq_term abstraction -> argument

val mk_eq_type : assumption -> ty -> ty -> eq_type
val mk_eq_term : assumption -> term -> term -> ty -> eq_term

val mk_term_convert : term -> assumption -> ty -> term

(** Make a non-abstracted constructor argument *)
val mk_not_abstract : 'a -> 'a abstraction

(** Abstract a term argument *)
val mk_abstract : Name.ident -> ty -> 'a abstraction -> 'a abstraction

(** [instantiate_term e0 ~lvl:k e] replaces bound variable [k] (defualt [0])  with term [e0] in term [e]. *)
val instantiate_term: term -> ?lvl:bound -> term -> term

(** [instantiate_term e0 ~lvl:k t] replaces bound variable [k] (default [0]) with term [e0] in type [t]. *)
val instantiate_type: term -> ?lvl:bound -> ty -> ty

(** [instantiate_abstraction inst_u inst_v e0 ~lvl:k abstr] instantiates bound variable
    [k] (default [0]) with term [e0] in the given abstraction. *)
val instantiate_abstraction :
  (term -> ?lvl:bound -> 'a -> 'a) ->
  term -> ?lvl:bound -> 'a abstraction -> 'a abstraction

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

(** [alpha_equal_type t1 t2] returns [true] if types [t1] and [t2] are alpha equal. *)
val alpha_equal_type : ty -> ty -> bool

val occurs_term : bound -> term -> bool

val occurs_type : bound -> ty -> bool

val occurs_eq_type : bound -> eq_type -> bool

val occurs_eq_term : bound -> eq_term -> bool

type print_env = private
  { forbidden : Name.ident list ;
    atoms : Name.atom_printer ; }

(** Forbid the given identifier from being used as a bound variable. *)
val add_forbidden : Name.ident -> print_env -> print_env

(** [print_abstraction occurs_v print_v ?max_level ~penv abstr ppf] prints an abstraction using formatter [ppf]. *)
val print_abstraction :
   (bound -> 'a -> bool) ->
   (?max_level:Level.t -> penv:print_env -> 'a -> Format.formatter -> unit) ->
   ?max_level:Level.t ->
   penv:print_env ->
   'a abstraction ->
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
