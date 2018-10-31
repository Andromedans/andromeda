(** Abstract syntax of type-theoretic types and terms *)

(** The type of bound variables. This type must necessarily be abstract and it must have
   no constructors. We rely on this fact in the [instantiate_XYZ] functions below so that
   from the outside nobody can even pass in any level other than the default one. *)
type bound

val equal_bound : bound -> bound -> bool

(** We use locally nameless syntax: names for free variables and deBruijn
   indices for bound variables. *)

(** The type of TT types. *)
type ty = private
  (** a type constructor *)
  | TypeConstructor of Name.constant * argument list
  | TypeMeta of type_meta * term list

and term = private
  (** a free variable *)
  | TermAtom of atom

  (** a bound variable *)
  | TermBound of bound

  (** a term constructor *)
  | TermConstructor of Name.constant * argument list

  | TermMeta of term_meta * term list

  (** a term conversion from the natural type of the term to the given type, we do not
     allow two consecutive conversions *)
  | TermConvert of term * assumption * ty

and eq_type = private EqType of assumption * ty * ty

and eq_term = private EqTerm of assumption * term * term * ty

and assumption = (ty, premise_boundary) Assumption.t

and atom = private { atom_name : Name.atom ; atom_type : ty }

(** A meta variable describes the local context and the boundary of its
   judgement, which depends on the judgement form. *)
and 't meta = private { meta_name : Name.meta ; meta_type : 't }

and type_meta = type_boundary meta
and term_meta = term_boundary meta
and eq_type_meta = eq_type_boundary meta
and eq_term_meta = eq_term_boundary meta

and premise_boundary =
    | BoundaryType of type_boundary
    | BoundaryTerm of term_boundary
    | BoundaryEqType of eq_type_boundary
    | BoundaryEqTerm of eq_term_boundary

and type_boundary = unit abstraction
and term_boundary = ty abstraction
and eq_type_boundary = (ty * ty) abstraction
and eq_term_boundary = (term * term * ty) abstraction

(** An argument of a term or type constructor. *)
and argument = private
  | ArgIsType of ty abstraction
  | ArgIsTerm of term abstraction
  | ArgEqType of eq_type abstraction
  | ArgEqTerm of eq_term abstraction

(** An abstracted entity. *)
and 'a abstraction = private
  | NotAbstract of 'a
  | Abstract of Name.ident * ty * 'a abstraction


(** Term constructors, these do not check for legality of constructions. *)

(** Create a fresh atom of the given type. *)
val fresh_atom : Name.ident -> ty -> atom

(** Create the judgement that an atom has its type. *)
val mk_atom : atom -> term

val fresh_type_meta : Name.ident -> type_boundary -> type_meta
val fresh_term_meta : Name.ident -> term_boundary -> term_meta
val fresh_eq_type_meta : Name.ident -> eq_type_boundary -> eq_type_meta
val fresh_eq_term_meta : Name.ident -> eq_term_boundary -> eq_term_meta

val mk_type_meta : type_meta -> term list -> ty
val mk_term_meta : term_meta -> term list -> term

(** Create a bound variable (it's a hole in a derivation?) *)
val mk_bound : bound -> term

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

(** Make a term conversion. It is illegal to pile a term conversion on top of another term
   conversion. *)
val mk_term_convert : term -> assumption -> ty -> term

(** Make a non-abstracted constructor argument *)
val mk_not_abstract : 'a -> 'a abstraction

(** Abstract a term argument *)
val mk_abstract : Name.ident -> ty -> 'a abstraction -> 'a abstraction

(** [instantiate_term e0 ~lvl:k e] replaces bound variable [k] (defualt [0]) with term
   [e0] in term [e]. Even though [lvl] is an optional argument here, it is of abstract
   type [bound] which prevents us from passing in any value of [lvl] other than the
   default one. *)
val instantiate_term: term -> ?lvl:bound -> term -> term

(** [instantiate_term e0 ~lvl:k t] replaces bound variable [k] (default [0]) with term [e0] in type [t]. *)
val instantiate_type: term -> ?lvl:bound -> ty -> ty

(** [instantiate_eq_type e0 ~lvl:k eq] replaces bound variable [k] (default [0])
   with term [e0] in equation [eq]. *)
val instantiate_eq_type : term -> ?lvl:bound -> eq_type -> eq_type

(** [instantiate_eq_term e0 ~lvl:k eq] replaces bound variable [k] (default [0])
   with term [e0] in equation [eq]. *)
val instantiate_eq_term : term -> ?lvl:bound -> eq_term -> eq_term

(** [instantiate_abstraction inst_u e0 ~lvl:k abstr] instantiates bound variable [k]
   (default [0]) with term [e0] in the given abstraction. *)
val instantiate_abstraction :
  (term -> ?lvl:bound -> 'a -> 'a) ->
  term -> ?lvl:bound -> 'a abstraction -> 'a abstraction

(** [fully_instantiate_abstraction inst_u ~lvl:k es abstr] fully instantiates abstraction [abstr] with the given terms
    [es]. All bound variables are eliminated. *)
val fully_instantiate_abstraction : (?lvl:bound -> term list -> 'a -> 'a) -> ?lvl:bound -> term list -> 'a abstraction -> 'a abstraction

(** [fully_instantiate_type ~lvl:k es t] fully instantiates type [t] with the given [es]. All bound variables are eliminated. *)
val fully_instantiate_type : ?lvl:bound -> term list -> ty -> ty

(** [fully_instantiate_term ~lvl:k es e] fully instantiates term [e] with the given [es]. All bound variables are eliminated. *)
val fully_instantiate_term : ?lvl:bound -> term list -> term -> term

(** [unabstract_type x t1 t2] instantiates bound variable [0] in [t2] with a fresh atom of type [t1].
    The freshly generated atom is returned, as well as the type. *)
val unabstract_type : Name.ident -> ty ->  ty -> atom * ty

(** [unabstract_term x t e] instantiates bound variable [0] in [e] with a fresh atom of type [t].
    The freshly generated atom is returned, as well as the type. *)
val unabstract_term : Name.ident -> ty ->  term -> atom * term

(** [unabstract_eq_type x t eq] instantiates bound variable [0] in [eq] with a fresh atom of type [t].
    The freshly generated atom is returned, as well as the type. *)
val unabstract_eq_type : Name.ident -> ty ->  eq_type -> atom * eq_type

(** [unabstract_eq_term x t eq] instantiates bound variable [0] in [eq] with a fresh atom of type [t].
    The freshly generated atom is returned, as well as the type. *)
val unabstract_eq_term : Name.ident -> ty ->  eq_term -> atom * eq_term

(** [unabstract_abstraction inst_u x t abstr] instantiates bond variable [0] in [abstr] with a fresh atom of type [t].
    The freshly generated atom is returned, as well as the type. *)
val unabstract_abstraction :
  (term -> ?lvl:bound -> 'a -> 'a) -> Name.ident -> ty -> 'a abstraction -> atom * 'a abstraction

(** [abstract_term x0 ~lvl:k t] replaces atom [x0] in type [t] with bound variable [k] (default [0]). *)
val abstract_type : Name.atom -> ?lvl:bound -> ty -> ty

(** [abstract_term x0 ~lvl:k e] replaces atom [x0] in term [e] with bound variable [k] (default [0]). *)
val abstract_term : Name.atom -> ?lvl:bound -> term -> term

(** [abstract_eq_type x0 ~lvl:k eq] replaces atom [x0] in equation [eq] with bound variable [k] (default [0]). *)
val abstract_eq_type : Name.atom -> ?lvl:bound -> eq_type -> eq_type

(** [abstract_eq_term x0 ~lvl:k eq] replaces atom [x0] in equation [eq] with bound variable [k] (default [0]). *)
val abstract_eq_term : Name.atom -> ?lvl:bound -> eq_term -> eq_term

(** [abstract_abstraaction abstract_u x0 ~lvl:k abstr] replaces atom [x0] in
   abstraction [abstr] with bound variable [k] (default [0]). *)
val abstract_abstraction :
  (Name.atom -> ?lvl:bound -> 'a -> 'a) ->
  Name.atom -> ?lvl:bound -> 'a abstraction -> 'a abstraction

(** abstract followed by instantiate *)
val substitute_term : term -> Name.atom -> term -> term

val substitute_type : term -> Name.atom -> ty -> ty

(** The asssumptions used by a term. Caveat: alpha-equal terms may have different assumptions. *)
val assumptions_term : ?lvl:bound -> term -> assumption

(** The assumptions used by a type. Caveat: alpha-equal types may have different assumptions. *)
val assumptions_type : ?lvl:bound -> ty -> assumption

val assumptions_eq_type : ?lvl:bound -> eq_type -> assumption

val assumptions_eq_term : ?lvl:bound -> eq_term -> assumption

val assumptions_arguments : argument list -> assumption

val assumptions_abstraction :
  (?lvl:bound -> 'a -> assumption) -> ?lvl:bound -> 'a abstraction -> assumption

(** Compute the list of atoms occurring in an abstraction. Similar to
    assumptions_XYZ functions, but allows use of the assumptions as atoms.
    May only be called on closed terms. *)
val context_abstraction :
  (?lvl:bound -> 'a -> assumption) -> 'a abstraction -> atom list

(** [alpha_equal_term e1 e2] returns [true] if term [e1] and [e2] are alpha equal. *)
val alpha_equal_term : term -> term -> bool

(** [alpha_equal_type t1 t2] returns [true] if types [t1] and [t2] are alpha equal. *)
val alpha_equal_type : ty -> ty -> bool

val alpha_equal_abstraction
  : ('a -> 'a -> bool) -> 'a abstraction -> 'a abstraction -> bool

val occurs_term : bound -> term -> bool

val occurs_type : bound -> ty -> bool

val occurs_eq_type : bound -> eq_type -> bool

val occurs_eq_term : bound -> eq_term -> bool

(* XXX Printing names is a trusted activity, thus the atom printing and all
   trusted parts of name management should probably be moved to the nucleus,
   at which time print_env can be made abstract. *)
type print_env =
  { forbidden : Name.ident list
  ; metas : Name.meta_printer
  ; atoms : Name.atom_printer
  }

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
