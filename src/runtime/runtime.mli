(** Runtime values and computations *)

(** {6 Values} *)

(** An AML reference cell. *)
type ref

(** An AML dynamic variable. *)
type dyn

(** values are "finished" or "computed". They are inert pieces of data. *)
type value = private
  | IsTerm of Jdg.is_term_abstraction    (** A term judgment *)
  | IsType of Jdg.is_type_abstraction    (** A type judgment *)
  | EqTerm of Jdg.eq_term_abstraction    (** A term equality *)
  | EqType of Jdg.eq_type_abstraction    (** A type equality *)
  | Closure of (value,value) closure     (** An AML function *)
  | Handler of handler                   (** Handler value *)
  | Tag of Name.ident * value list       (** Application of a data constructor *)
  | Tuple of value list                  (** Tuple of values *)
  | Ref of ref                           (** Ref cell *)
  | Dyn of dyn                           (** Dynamic variable *)
  | String of string                     (** String constant (opaque, not a list) *)

and operation_args = { args : value list; checking : Jdg.is_type_abstraction option }

(** A handler contains AML code for handling zero or more operations,
    plus the default case *)
and handler

(** Maps an ['a] to a ['b comp]. In practice ['b] is usually [value] *)
and ('a,'b) closure

(** a descriptive name of a value, e.g. the name of [Handler _] is ["a handler"] *)
val name_of : value -> string

(** {b Value construction} *)

(** Build an [IsTerm] value *)
val mk_is_term : Jdg.is_term_abstraction -> value

(** Build an [IsType] value *)
val mk_is_type : Jdg.is_type_abstraction -> value

(** Build an [EqTerm] value *)
val mk_eq_term : Jdg.eq_term_abstraction -> value

(** Build an [EqType] value *)
val mk_eq_type : Jdg.eq_type_abstraction -> value

(** Build a [Handler] value *)
val mk_handler : handler -> value

(** Build a [Tag] value *)
val mk_tag     : Name.ident -> value list -> value

(** Build a [Tuple] value *)
val mk_tuple   : value list -> value

(** Build a [String] value *)
val mk_string  : string -> value


(** {b Value extraction} *)

(** Convert, or fail with [IsTermExpected] *)
val as_is_term : loc:Location.t -> value -> Jdg.is_term

(** Convert, or fail with [IsTypeExpected] *)
val as_is_type : loc:Location.t -> value -> Jdg.is_type

(** Convert, or fail with [EqTermExpected] *)
val as_eq_term : loc:Location.t -> value -> Jdg.eq_term

(** Convert, or fail with [EqTypeExpected] *)
val as_eq_type : loc:Location.t -> value -> Jdg.eq_type

(** Convert, or fail with [IsTermAbstractionExpected] *)
val as_is_term_abstraction : loc:Location.t -> value -> Jdg.is_term_abstraction

(** Convert, or fail with [IsTypeAbstractionExpected] *)
val as_is_type_abstraction : loc:Location.t -> value -> Jdg.is_type_abstraction

(** Convert, or fail with [EqTermAbstractionExpected] *)
val as_eq_term_abstraction : loc:Location.t -> value -> Jdg.eq_term_abstraction

(** Convert, or fail with [EqTypeAbstractionExpected] *)
val as_eq_type_abstraction : loc:Location.t -> value -> Jdg.eq_type_abstraction

(** Convert, or fail with [ClosureExpected] *)
val as_closure : loc:Location.t -> value -> (value,value) closure

(** Convert, or fail with [HandlerExpected] *)
val as_handler : loc:Location.t -> value -> handler

(** Convert, or fail with [RefExpected] *)
val as_ref : loc:Location.t -> value -> ref

(** Convert, or fail with [DynExpected] *)
val as_dyn : loc:Location.t -> value -> dyn

(** Convert, or fail with [StringExpected] *)
val as_string : loc:Location.t -> value -> string


(** {b Other operations} *)

(** Check whether two values are equal. *)
val equal_value: value -> value -> bool

(** Check whether the given value represents an AML list *)
val as_list_opt : value -> value list option

(** Pretty-print a value. *)
val print_value : ?max_level:Level.t -> penv:TT.print_env -> value -> Format.formatter -> unit


(** {6 Error Handling} *)

(** The runtime errors *)
type error =
  | ExpectedAtom of Jdg.is_term
  | UnknownExternal of string
  | UnknownConfig of string
  | Inapplicable of value
  | AnnotationMismatch of Jdg.is_type * Jdg.is_type
  | TypeMismatchCheckingMode of Jdg.is_term_abstraction * Jdg.is_type_abstraction
  | EqualityFail of Jdg.is_term * Jdg.is_term
  | UnannotatedAbstract of Name.ident
  | MatchFail of value
  | FailureFail of value
  | InvalidEqualTerm of Jdg.is_term * Jdg.is_term
  | InvalidEqualType of Jdg.is_type * Jdg.is_type
  | ListExpected of value
  | OptionExpected of value
  | IsTypeExpected of value
  | IsTermExpected of value
  | EqTypeExpected of value
  | EqTermExpected of value
  | IsTypeAbstractionExpected of value
  | IsTermAbstractionExpected of value
  | EqTypeAbstractionExpected of value
  | EqTermAbstractionExpected of value
  | JudgementExpected of value
  | ClosureExpected of value
  | HandlerExpected of value
  | RefExpected of value
  | DynExpected of value
  | StringExpected of value
  | CoercibleExpected of value
  | InvalidConvertible of Jdg.is_type * Jdg.is_type * Jdg.eq_type
  | InvalidCoerce of Jdg.is_type * Jdg.is_term
  | UnhandledOperation of Name.operation * value list

(** The exception that is raised on runtime error *)
exception Error of error Location.located

(** Pretty-print a runtime error *)
val print_error : penv:TT.print_env -> error -> Format.formatter -> unit

(** Report a runtime error (raises an Error exception) *)
val error : loc:Location.t -> error -> 'a


(** {6 Computation} *)

(** computations provide a dynamically scoped environment and operations *)
type 'a comp

val mk_closure : (value -> value comp) -> value

(** {b Monadic structure} *)

val bind: 'a comp -> ('a -> 'b comp)  -> 'b comp
val return : 'a -> 'a comp


(** {b Monadic shorthand} *)

val return_unit : value comp

val return_is_term : Jdg.is_term_abstraction -> value comp
val return_is_type : Jdg.is_type_abstraction -> value comp
val return_eq_term : Jdg.eq_term_abstraction -> value comp
val return_eq_type : Jdg.eq_type_abstraction -> value comp

val return_closure : (value -> value comp) -> value comp
val return_handler :
   (value -> value comp) option ->
   (operation_args -> value comp) Name.IdentMap.t ->
   (value -> value comp) option ->
   value comp

(** {b Monadic interface} *)

(** A computation that applies the given closure to the given argument
    and produces the result. *)
val apply_closure : ('a,'b) closure -> 'a -> 'b comp

(** A computation that creates and returns a new reference cell. *)
val mk_ref : value -> value comp

(** A computation that dereferences the given reference cell. *)
val lookup_ref : ref -> value comp

(** A computation that updates the given reference cell with the given value. *)
val update_ref : ref -> value -> unit comp

(** A computation that invokes the specified operation. *)
val operation : Name.operation -> ?checking:Jdg.is_type_abstraction -> value list -> value comp

(** Wrap the given computation with a handler. *)
val handle_comp : handler -> value comp -> value comp

(** Wrap the given computation with a dynamic variable binding. *)
val now : dyn -> value -> 'a comp -> 'a comp

(** Lookup the current continuation. Only usable while handling an operation. *)
val continue : loc:Location.t -> value -> value comp

(** Get the printing environment from the monad *)
val lookup_penv : TT.print_env comp

(** Gets the current rules of inference. *)
val lookup_signature : Jdg.Signature.t comp

(** Bound and free variable stuff *)

(** Add a bound variable to the environment. *)
val add_bound : value -> 'a comp -> 'a comp

val add_bound_rec :
  (value -> value comp) list -> 'a comp -> 'a comp

(** [index_of_level n] gives the De Bruijn index of the variable whose De Bruijn level is [n]. *)
val index_of_level : Rsyntax.level -> Rsyntax.bound comp

(** [add_free ~loc x (ctx,t) f] generates a fresh atom [y] from identifier [x],
    then it extends [ctx] to [ctx' = ctx, y : t]
    and runs [f (ctx' |- y : t)] in the environment with [x] bound to [ctx' |- y : t].
    NB: This is an effectful computation, as it increases a global counter. *)
val add_free: Name.ident -> Jdg.is_type -> (Jdg.is_atom -> 'a comp) -> 'a comp

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : loc:Location.t -> int -> value comp

(** Lookup the current value of a dynamic variable. *)
val lookup_dyn : dyn -> value comp

(** {6 Toplevel} *)

(** state environment, no operations *)
type 'a toplevel

(** {b Monadic structure } *)

val top_bind : 'a toplevel -> ('a -> 'b toplevel) -> 'b toplevel
val top_return : 'a -> 'a toplevel

(** {b Monadic shorthand} *)

val top_return_closure : ('a -> 'b comp) -> ('a,'b) closure toplevel

val top_fold : ('a -> 'b -> 'a toplevel) -> 'a -> 'b list -> 'a toplevel

(** {b Monadic interface} *)

(** Add a bound variable with the given name to the environment. *)
val add_topbound : value -> unit toplevel

(** Add a list of mutually recursive definitions to the toplevel environment. *)
val add_topbound_rec : (value -> value comp) list -> unit toplevel

(** Add a dynamic variable. *)
val add_dynamic : loc:Location.t -> Name.ident -> value -> unit toplevel

(** Add a top-level handler case to the environment. *)
val add_handle : Name.ident -> (value list * Jdg.is_type_abstraction option, value) closure
                 -> unit toplevel

(** Modify the value bound by a dynamic variable *)
val top_now : dyn -> value -> unit toplevel

(** Handle a computation at the toplevel. *)
val top_handle : loc:Location.t -> 'a comp -> 'a toplevel

(** Get the printing environment from the toplevel monad *)
val top_lookup_penv : TT.print_env toplevel

type 'a caught =
  | CaughtJdg of Jdg.error Location.located
  | CaughtRuntime of error Location.located
  | Result of 'a

(** Catch Error exceptions. The state is not changed if an exception occurs. *)
val catch : loc:Location.t -> 'a toplevel Lazy.t -> 'a caught toplevel

(** {6 Running a toplevel computation} *)

(** toplevel environment *)
type topenv

(** The empty toplevel environment. *)
val empty : topenv

(** Execute a toplevel command in the given environment. *)
val exec : 'a toplevel -> topenv -> 'a * topenv

(** {6 Poorly-Documented Functions used by Matching } *)

(** Runtime environment *)
type env

(** Extract the current environment (for matching) *)
val get_env : env comp

(** Get the toplevel environment from the toplevel monad *)
val top_get_env : env toplevel

val get_signature : env -> Jdg.Signature.t

(** For matching *)
val get_bound : loc:Location.t -> int -> env -> value

(** Add a bound variable (for matching). *)
val push_bound : value -> env -> env

(** {6 Conversion to JSON} *)

module Json :
sig
  val value : value -> Json.t
end
