(** Runtime values and computations *)

(** The type of an AML reference. *)
type ref

(** Runtime environment *)
type env

type ('a,'b) closure

(** The values are "finished" or "computed". They are inert pieces of data. *)
type value = private
  | Term of Jdg.term
  | Closure of (value,value) closure
  | Handler of handler
  | Tag of Name.ident * value list
  | Tuple of value list
  | Ref of ref
  | String of string (** NB: strings are opaque to the user, ie not lists *)

and operation_args = { args : value list; checking : Jdg.ty option}

and handler

(** computations provide a dynamically scoped environment and operations *)
type 'a comp

(** state environment, no operations *)
type 'a toplevel

(** the runtime errors *)
type error =
  | ExpectedAtom of Jdg.term
  | UnknownExternal of string
  | UnknownConfig of string
  | Inapplicable of value
  | TypeMismatch of Jdg.ty * Jdg.ty
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
  | RefExpected of value
  | StringExpected of value
  | CoercibleExpected of value
  | UnhandledOperation of Name.operation * value list

(** The exception that is raised on runtime error *)
exception Error of error Location.located

(** Report a runtime error (fails irrevocably) *)
val error : loc:Location.t -> error -> 'a

(** a descriptive name of a value, e.g. the name of [Handler _] is ["a handler"] *)
val name_of : value -> string

(** Make values *)
val mk_term : Jdg.term -> value
val mk_handler : handler -> value
val mk_tag : Name.ident -> value list -> value
val mk_tuple : value list -> value
val mk_string : string -> value

val apply_closure : ('a,'b) closure -> 'a -> 'b comp

(** References *)
val mk_ref : value -> value comp

val lookup_ref : ref -> value comp

val update_ref : ref -> value -> unit comp

(** Monadic primitives *)
val bind: 'a comp -> ('a -> 'b comp)  -> 'b comp

val top_bind : 'a toplevel -> ('a -> 'b toplevel) -> 'b toplevel

type 'a caught =
  | CaughtJdg of Jdg.error Location.located
  | CaughtRuntime of error Location.located
  | Value of 'a

(** Catch exceptions. The state is not changed if an exception is caught. *)
val catch : 'a toplevel Lazy.t -> 'a caught toplevel

val top_return : 'a -> 'a toplevel
val return : 'a -> 'a comp

(* XXX why do we need all of these? *)
val top_return_closure : ('a -> 'b comp) -> ('a,'b) closure toplevel
val top_mk_closure : (value -> value comp) -> value toplevel
val return_closure : (value -> value comp) -> value comp

val return_term : Jdg.term -> value comp
val return_unit : value comp

val return_handler :
   (value -> value comp) option ->
   (operation_args -> value comp) Name.IdentMap.t ->
   (value -> value comp) option ->
   value comp

val top_fold : ('a -> 'b -> 'a toplevel) -> 'a -> 'b list -> 'a toplevel

(** Pretty-print a value. *)
val as_list_opt : value -> value list option

val print_value : ?max_level:Level.t -> penv:TT.print_env -> value -> Format.formatter -> unit

val print_error : penv:TT.print_env -> error -> Format.formatter -> unit

(** Coerce values *)
val as_term : loc:Location.t -> value -> Jdg.term
val as_closure : loc:Location.t -> value -> (value,value) closure
val as_handler : loc:Location.t -> value -> handler
val as_ref : loc:Location.t -> value -> ref
val as_string : loc:Location.t -> value -> string

(** Operations *)
val operation : Name.operation -> ?checking:Jdg.ty -> value list -> value comp

(** Extract the current environment (for matching) *)
val get_env : env comp

(** Typing environment *)
val get_typing_env : env -> Jdg.Env.t

val lookup_typing_env : Jdg.Env.t comp

(** Lookup abstracting variables. *)
val lookup_abstracting : value list comp

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : loc:Location.t -> int -> value comp

(** For matching *)
val get_bound : loc:Location.t -> int -> env -> value

(** Add a bound variable to the environment. *)
val add_bound : value -> 'a comp -> 'a comp

val add_bound_rec :
  (value -> value comp) list -> 'a comp -> 'a comp

(** Modify the value bound by a dynamic variable *)
val now : loc:Location.t -> int -> value -> 'a comp -> 'a comp

val top_now : loc:Location.t -> int -> value -> unit toplevel

(** Add a bound variable (for matching). *)
val push_bound : value -> env -> env

(** [add_free ~loc x (ctx,t) f] generates a fresh atom [y] from identifier [x],
    then it extends [ctx] to [ctx' = ctx, y : t]
    and runs [f (ctx' |- y : t)] in the environment with [x] bound to [ctx' |- y : t].
    NB: This is an effectful computation, as it increases a global counter. *)
val add_free: loc:Location.t -> Name.ident -> Jdg.ty -> (Jdg.atom -> 'a comp) -> 'a comp

val add_abstracting : value -> 'a comp -> 'a comp

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

(** Lookup the current continuation. *)
val continue : loc:Location.t -> value -> value comp

(** Get the printing environment from the monad *)
val lookup_penv : TT.print_env comp

(** Get the printing environment from the toplevel monad *)
val top_lookup_penv : TT.print_env toplevel

(** Interface to execute suspended computations. *)
type topenv

(** Get the printing environment from the toplevel environment. *)
val get_penv : topenv -> TT.print_env

(** The empty toplevel environment. *)
val empty : topenv

(** Execute a toplevel command in the given environment. *)
val exec : 'a toplevel -> topenv -> 'a * topenv

(** Handling *)
val handle_comp : handler -> value comp -> value comp

(** Handle a computation at the toplevel. *)
val top_handle : loc:Location.t -> 'a comp -> 'a toplevel

(** Check whether two values are equal. *)
val equal_value: value -> value -> bool

module Json :
sig
  val value : value -> Json.t
end
