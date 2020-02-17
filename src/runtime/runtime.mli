(** Runtime values and computations *)

(** {6 Values} *)

type ml_constructor = Ident.t

(** values are "finished" or "computed". They are inert pieces of data. *)
type value =
  | Judgement of Nucleus.judgement_abstraction (** A judgement *)
  | Boundary of Nucleus.boundary_abstraction   (** A judgement boundary (also known as a goal) *)
  | Derivation of Nucleus.derivation           (** A hypothetical derivation *)
  | External of external_value                 (** An external ML value *)
  | Closure of (value,value) closure           (** An ML function *)
  | Handler of handler                         (** Handler value *)
  | Exc of exc                                 (** An exception *)
  | Tag of ml_constructor * value list         (** Application of a data constructor *)
  | Tuple of value list                        (** Tuple of values *)
  | Ref of value ref                           (** Ref cell *)
  | String of string                           (** String constant (opaque, not a list) *)

and exc = Ident.t * value option

and external_value =
  | EqualityChecker of Eqchk.checker

and operation_args = { args : value list; checking : Nucleus.boundary_abstraction option }

(** A handler contains ML code for handling zero or more operations,
    plus the default case *)
and handler

(** Maps an ['a] to a ['b comp]. In practice ['b] is usually [value] *)
and ('a,'b) closure

(** A descriptive name of a value, e.g. the name of [Handler _] is ["a handler"] *)
val name_of : value -> string

(** Are ML constructors equal? *)
val equal_tag : ml_constructor -> ml_constructor -> bool

(** {b Value construction} *)

(** Build an abstracted judgement as a value *)
val mk_judgement : Nucleus.judgement_abstraction -> value

(** Build an abstracted boundary as a value *)
val mk_boundary : Nucleus.boundary_abstraction -> value

(** Build a [Handler] value *)
val mk_handler : handler -> value

(** Build a [Tag] value *)
val mk_tag : ml_constructor -> value list -> value

(** Build a [Tuple] value *)
val mk_tuple : value list -> value

(** Build a [String] value *)
val mk_string : string -> value


(** {b Value extraction} *)

(** Convert to an equality checker, or fail with [EqualityCheckerExcpected] *)
val as_equality_checker : at:Location.t -> value -> Eqchk.checker

(** Convert to a derivation, or fail with [DerivationExpected] *)
val as_derivation : at:Location.t -> value -> Nucleus.derivation

(** Convert to a non-abstracted value, or fail with [UnexpectedAbstraction] *)
val as_not_abstract : at:Location.t -> 'a Nucleus.abstraction -> 'a

(** Convert, or fail with [IsTermExpected] *)
val as_is_term : at:Location.t -> value -> Nucleus.is_term

(** Convert, or fail with [IsTypeExpected] *)
val as_is_type : at:Location.t -> value -> Nucleus.is_type

(** Convert, or fail with [EqTermExpected] *)
val as_eq_term : at:Location.t -> value -> Nucleus.eq_term

(** Convert, or fail with [EqTypeExpected] *)
val as_eq_type : at:Location.t -> value -> Nucleus.eq_type

(** Convert, or fail with [JudgementExpected] *)
val as_judgement : at:Location.t -> value -> Nucleus.judgement

(** Convert, or fail with [IsTermAbstractionExpected] *)
val as_is_term_abstraction : at:Location.t -> value -> Nucleus.is_term_abstraction

(** Convert, or fail with [IsTypeAbstractionExpected] *)
val as_is_type_abstraction : at:Location.t -> value -> Nucleus.is_type_abstraction

(** Convert, or fail with [EqTermAbstractionExpected] *)
val as_eq_term_abstraction : at:Location.t -> value -> Nucleus.eq_term_abstraction

(** Convert, or fail with [EqTypeAbstractionExpected] *)
val as_eq_type_abstraction : at:Location.t -> value -> Nucleus.eq_type_abstraction

(** Convert, or fail with [JudgementAbstractionExpected] *)
val as_judgement_abstraction : at:Location.t -> value -> Nucleus.judgement_abstraction

(** Convert, or fail with [BoundaryAbstractionExpected] *)
val as_boundary_abstraction : at:Location.t -> value -> Nucleus.boundary_abstraction

(** Convert, or fail with [ClosureExpected] *)
val as_closure : at:Location.t -> value -> (value,value) closure

(** Convert, or fail with [HandlerExpected] *)
val as_handler : at:Location.t -> value -> handler

(** Convert, or fail with [ExceptionExpected] *)
val as_exception : at:Location.t -> value -> exc

(** Convert, or fail with [RefExpected] *)
val as_ref : at:Location.t -> value -> value ref

(** Convert, or fail with [StringExpected] *)
val as_string : at:Location.t -> value -> string

(** Convert, or fail with [BoolExpected] *)
val as_bool : at:Location.t -> value -> bool


(** {b Other operations} *)

(** Check whether two values are equal. *)
val equal_value: value -> value -> bool

(** Check whether the given value represents an ML list *)
(* val as_list_opt : value -> value list option *)

(** printing environment *)
type penv = {
  forbidden : Name.set ;
  opens : Path.set;
  signature : Nucleus.signature
}

(** Pretty-print a value. *)
val print_value :
  ?max_level:Level.t -> penv:penv -> value -> Format.formatter -> unit


(** {6 Error Handling} *)

(** The runtime errors *)
type error =
  | TooFewArguments
  | TooManyArguments
  | ExpectedAtom of Nucleus.is_term
  | UnknownExternal of string
  | UnknownConfig of string
  | Inapplicable of value
  | TypeMismatchCheckingMode of Nucleus.judgement_abstraction * Nucleus.boundary_abstraction
  | UnexpectedAbstraction
  | TermEqualityFail of Nucleus.is_term * Nucleus.is_term
  | TypeEqualityFail of Nucleus.is_type * Nucleus.is_type
  | UnannotatedAbstract of Name.t
  | MatchFail of value
  | InvalidComparison
  | InvalidEqualTerm of Nucleus.is_term * Nucleus.is_term
  | InvalidEqualType of Nucleus.is_type * Nucleus.is_type
  | BoolExpected of value
  | ListExpected of value
  | OptionExpected of value
  | IsTypeExpected of value
  | IsTermExpected of value
  | EqTypeExpected of value
  | EqTermExpected of value
  | AbstractionExpected
  | JudgementExpected of value
  | JudgementOrBoundaryExpected of value
  | EqualityCheckerExpected of value
  | DerivationExpected of value
  | ClosureExpected of value
  | HandlerExpected of value
  | RefExpected of value
  | ExceptionExpected of value
  | StringExpected of value
  | CoercibleExpected of value
  | InvalidConvert of Nucleus.judgement_abstraction * Nucleus.eq_type_abstraction
  | InvalidCoerce of Nucleus.judgement_abstraction * Nucleus.boundary_abstraction
  | UnhandledOperation of Ident.t * value list
  | UncaughtException of Ident.t * value option
  | InvalidPatternMatch of value

(** The exception that is raised on runtime error *)
exception Error of error Location.located

(** Pretty-print a runtime error *)
val print_error : penv:penv -> error -> Format.formatter -> unit

(** Report a runtime error (raises an Error exception) *)
val error : at:Location.t -> error -> 'a


(** {6 Computation} *)

(** computations provide a dynamically scoped environment and operations *)
type 'a comp

(** Convert an external function to a closure. Only use this when the function
   does not access its lexical scope, i.e., when it is an external OCaml
   function that does not care what lexical environment it is run in. *)
val mk_closure_external : (value -> value comp) -> value

(** {b Monadic structure} *)

(** Monadic bind *)
val bind: 'a comp -> ('a -> 'b comp)  -> 'b comp

(** Return a value *)
val return : 'a -> 'a comp

val raise_exception : exc -> 'a comp

(** {b Monadic shorthand} *)

val return_unit : value comp

val return_judgement : Nucleus.judgement_abstraction -> value comp

val return_boundary : Nucleus.boundary_abstraction -> value comp

val return_closure : (value -> value comp) -> value comp

val return_handler :
   (value -> value comp) option ->
   (operation_args -> value comp) Ident.map ->
   (exc -> value comp) ->
   value comp

(** {b Monadic interface} *)

(** A computation that applies the given closure to the given argument
    and produces the result. *)
val apply_closure : ('a,'b) closure -> 'a -> 'b comp

(** A computation that creates and returns a new reference cell. *)
val mk_ref : value -> value comp

(** A computation that dereferences the given reference cell. *)
val lookup_ref : value ref -> value comp

(** A computation that updates the given reference cell with the given value. *)
val update_ref : value ref -> value -> unit comp

(** A computation that invokes the specified operation. *)
val operation : Ident.t -> ?checking:Nucleus.boundary_abstraction -> value list -> value comp

(** Wrap the given computation with a handler. *)
val handle_comp : handler -> value comp -> value comp

(** Get the printing environment *)
val lookup_penv : penv comp

(** Get the printing environment *)
val lookup_nucleus_penv : Nucleus.print_environment comp

(** Gets the current rules of inference. *)
val lookup_signature : Nucleus.signature comp

(** Bound and free variable stuff *)

(** Add a bound variable to the environment. *)
val add_bound : value -> 'a comp -> 'a comp

val add_bound_rec :
  (value -> value comp) list -> 'a comp -> 'a comp

(** [add_free ~loc x t f] generates a fresh atom [a] from identifier [x],
    and runs [f a] in the environment extended with [a : t].
    NB: This is an effectful computation, as it increases a global counter. *)
val add_free: Name.t -> Nucleus.is_type -> (Nucleus.is_atom -> 'a comp) -> 'a comp

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : Path.index -> value comp

(** Lookup a value *)
val lookup_ml_value : Path.t -> value comp

(** {6 Toplevel} *)

(** {b Monadic structure of top-level} *)

(** Top-level computation monad *)
type 'a toplevel

val top_bind : 'a toplevel -> ('a -> 'b toplevel) -> 'b toplevel
val top_return : 'a -> 'a toplevel

(** {b Monadic shorthand} *)

val top_return_closure : ('a -> 'b comp) -> ('a,'b) closure toplevel

val top_fold : ('a -> 'b -> 'a toplevel) -> 'a -> 'b list -> 'a toplevel

(** Evaluate a top-level computation as an ML module *)
val top_as_ml_module : unit toplevel -> unit toplevel

(** {b Monadic interface} *)

(** Add a bound variable with the given name to the environment. *)
val top_add_ml_value : value -> unit toplevel

(** Add a list of mutually recursive definitions to the toplevel environment. *)
val top_add_ml_value_rec : (value -> value comp) list -> unit toplevel

(** Extend the signature with a new rule *)
val top_add_rule : Ident.t -> Nucleus.primitive -> unit toplevel

val top_add_handle :
  at:Location.t ->   Ident.t ->
  ((operation_args -> value comp) -> (operation_args -> value comp)) -> unit toplevel

(** Handle a computation at the toplevel. *)
val top_handle : at:Location.t -> 'a comp -> 'a toplevel

(** Lookup the current printing environment *)
val top_lookup_penv : penv toplevel

(** Lookup the currently open paths *)
val top_lookup_opens : Path.set toplevel

(** Open a module path *)
val top_open_path : Path.t -> unit toplevel

(** Get the signature from the toplevel monad *)
val top_lookup_signature : Nucleus.signature toplevel

(** {6 Running a toplevel computation} *)

(** Toplevel environment *)
type topenv

(** The empty toplevel environment. *)
val empty : topenv

(** Get the current printing environment. *)
val top_get_penv : topenv -> penv

(** Get the current printing environment for the nucleus *)
val top_get_nucleus_penv : topenv -> Nucleus.print_environment

(** Execute a toplevel command in the given environment. *)
val exec : 'a toplevel -> topenv -> 'a * topenv

(** {6 Poorly-Documented Functions used by Matching } *)

(** Runtime environment *)
type env

(** Extract the current environment (for matching) *)
val get_env : env comp

(** Run in the given environment (but not the state). *)
val with_env : env -> 'a comp -> 'a comp

(** Get the toplevel environment from the toplevel monad *)
val top_get_env : env toplevel

val get_signature : env -> Nucleus.signature

(** For matching *)
val get_bound : Path.index -> env -> value

(** Add a bound variable (for matching). *)
val push_bound : value -> env -> env

(** {6 Conversion to JSON} *)

module Json :
sig
  val value : value -> Json.t
end
