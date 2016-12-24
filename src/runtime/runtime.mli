(** Runtime values and computations *)

(** {6 Values} *)

(** values are "finished" or "computed". They are inert pieces of data. *)
type value = private
  | Term of Jdg.term                 (** A *typing* judgment built by the nucleus *)
  | Closure of (value,value) closure (** An AML function *)
  | Handler of handler               (** Handler value *)
  | Tag of Name.ident * value list   (** Application of a data constructor *)
  | Tuple of value list              (** Tuple of values *)
  | Ref of ref                       (** Ref cell *)
  | String of string                 (** String constant (opaque, not a list) *)

and operation_args = { args : value list; checking : Jdg.ty option}

(** A handler contains AML code for handling zero or more operations,
    plus the default case *)
and handler

(** Maps an ['a] to a ['b comp]. In practice ['b] is usually [value] *)
and ('a,'b) closure

(** An AML reference cell. *)
and ref

(** a descriptive name of a value, e.g. the name of [Handler _] is ["a handler"] *)
val name_of : value -> string

(** {b Value construction} *)

val mk_term    : Jdg.term   -> value                (** Builds a [Term] value *)
val mk_handler : handler    -> value                (** Builds a [Handler] value *)
val mk_tag     : Name.ident -> value list -> value  (** Builds a [Tag] value *)
val mk_tuple   : value list -> value                (** Builds a [Tuple] value *)
val mk_string  : string     -> value                (** Builds a [String] value *)

(** {b Value extraction} *)

val as_term : loc:Location.t -> value -> Jdg.term   (** Fails with [TermExpected] *)
val as_closure : loc:Location.t -> value -> (value,value) closure (** Fails with [ClosureExpected] *)
val as_handler : loc:Location.t -> value -> handler (** Fails with [HandlerExpected] *)
val as_ref : loc:Location.t -> value -> ref         (** Fails with [RefExpected] *)
val as_string : loc:Location.t -> value -> string   (** Fails with [StringExpected] *)

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
  | ExpectedAtom of Jdg.term
  | UnknownExternal of string
  | UnknownConfig of string
  | Inapplicable of value
  | AnnotationMismatch of Jdg.ty * Jdg.ty
  | TypeMismatchCheckingMode of Jdg.term * Jdg.ty
  | EqualityFail of Jdg.term * Jdg.term
  | UnannotatedLambda of Name.ident
  | MatchFail of value
  | FailureFail of value
  | InvalidEqual of Jdg.ty
  | EqualityTypeExpected of Jdg.ty
  | InvalidAsEquality of Jdg.ty
  | ProductExpected of Jdg.ty
  | InvalidAsProduct of Jdg.ty
  | ListExpected of value
  | OptionExpected of value
  | TermExpected of value
  | ClosureExpected of value
  | HandlerExpected of value
  | FunctionExpected of Jdg.term
  | RefExpected of value
  | StringExpected of value
  | CoercibleExpected of value
  | InvalidConvertible of Jdg.ty * Jdg.ty * Jdg.eq_ty
  | InvalidCoerce of Jdg.ty * Jdg.term
  | InvalidFunConvertible of Jdg.ty * Jdg.eq_ty
  | InvalidFunCoerce of Jdg.term
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


(** {b Monadic structure} *)

val bind: 'a comp -> ('a -> 'b comp)  -> 'b comp
val return : 'a -> 'a comp


(** {b Monadic shorthand} *)

val return_unit : value comp

val return_term : Jdg.term -> value comp
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
val operation : Name.operation -> ?checking:Jdg.ty -> value list -> value comp

(** Wrap the given computation with a handler. *)
val handle_comp : handler -> value comp -> value comp

(** Wrap the given computation with a dynamic variable binding. *)
val now : loc:Location.t -> int -> value -> 'a comp -> 'a comp

(** Lookup the current continuation. Only usable while handling an operation. *)
val continue : loc:Location.t -> value -> value comp

(** Get the printing environment from the monad *)
val lookup_penv : TT.print_env comp

(** Gets the current constants *)
val lookup_typing_signature : Jdg.Signature.t comp

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
val add_free: loc:Location.t -> Name.ident -> Jdg.ty -> (Jdg.atom -> 'a comp) -> 'a comp

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : loc:Location.t -> int -> value comp

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

(** Add a constant of a given type to the environment. *)
val add_constant : loc:Location.t -> Name.ident -> Jdg.closed_ty -> unit toplevel

(** Add a bound variable with the given name to the environment. *)
val add_topbound : value -> unit toplevel

(** Add a list of mutually recursive definitions to the toplevel environment. *)
val add_topbound_rec : (value -> value comp) list -> unit toplevel

(** Add a dynamic variable. *)
val add_dynamic : loc:Location.t -> Name.ident -> value -> unit toplevel

(** Add a top-level handler case to the environment. *)
val add_handle : Name.ident -> (value list * Jdg.ty option,value) closure -> unit toplevel

(** Modify the value bound by a dynamic variable *)
val top_now : loc:Location.t -> int -> value -> unit toplevel

(** Handle a computation at the toplevel. *)
val top_handle : loc:Location.t -> 'a comp -> 'a toplevel

(** Get the printing environment from the toplevel monad *)
val top_lookup_penv : TT.print_env toplevel

type 'a caught =
  | CaughtJdg of Jdg.error Location.located
  | CaughtRuntime of error Location.located
  | Value of 'a

(** Catch Error exceptions. The state is not changed if an exception occurs. *)
val catch : 'a toplevel Lazy.t -> 'a caught toplevel

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

val get_typing_signature : env -> Jdg.Signature.t

(** For matching *)
val get_bound : loc:Location.t -> int -> env -> value

(** Add a bound variable (for matching). *)
val push_bound : value -> env -> env

(** {6 Conversion to JSON} *)

module Json :
sig
  val value : value -> Json.t
end
