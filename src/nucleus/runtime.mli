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
  | Ident of Name.ident

and operation_args = { args : value list; checking : Jdg.ty option}

and handler

(** computations provide a dynamically scoped environment and operations *)
type 'a comp

(** state environment, no operations *)
type 'a toplevel

val empty : env

(** a descriptive name of a value, e.g. the name of [Handler _] is ["a handler"] *)
val name_of : value -> string

(** Make values *)
val mk_term : Jdg.term -> value
val mk_handler : handler -> value
val mk_tag : Name.ident -> value list -> value
val mk_tuple : value list -> value
val mk_string : string -> value
val mk_ident : Name.ident -> value

val apply_closure : ('a,'b) closure -> 'a -> 'b comp

(** References *)
val mk_ref : value -> value comp

val lookup_ref : ref -> value comp

val update_ref : ref -> value -> unit comp

(** Monadic primitives *)
val bind: 'a comp -> ('a -> 'b comp)  -> 'b comp

val top_bind : 'a toplevel -> ('a -> 'b toplevel) -> 'b toplevel

(** Catch errors. The state is not changed if the command fails. *)
val catch : (unit -> 'a toplevel) -> ('a,Error.details) Error.res toplevel

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
val print_value : (?max_level:Level.t -> value -> Format.formatter -> unit) comp
val print_term : (?max_level:Level.t -> Tt.term -> Format.formatter -> unit) comp
val print_ty : (?max_level:Level.t -> Tt.ty -> Format.formatter -> unit) comp

val top_print_value : (?max_level:Level.t -> value -> Format.formatter -> unit) toplevel

(** Coerce values *)
val as_term : loc:Location.t -> value -> Jdg.term
val as_closure : loc:Location.t -> value -> (value,value) closure
val as_handler : loc:Location.t -> value -> handler
val as_ref : loc:Location.t -> value -> ref
val as_string : loc:Location.t -> value -> string
val as_ident : loc:Location.t -> value -> Name.ident

(** Operations *)
val operation : Name.operation -> ?checking:Jdg.ty -> value list -> value comp

(** Extract the current environment (for matching) *)
val get_env : env comp

(** Lookup a constant. *)
val get_constant : Name.constant -> env -> Tt.ty option

val lookup_constant : loc:Location.t -> Name.constant -> Tt.ty comp

(** Lookup a signature definition *)
val get_signature : Name.signature -> env -> Tt.sig_def option

(** Lookup a signature definition, monadically *)
val lookup_signature : loc:Location.t -> Name.signature -> Tt.sig_def comp

(** Find a signature with the given labels (in this exact order) *)
val find_signature : loc:Location.t -> Name.label list -> (Name.signature * Tt.sig_def) comp

(** Lookup abstracting variables. *)
val lookup_abstracting : value list comp

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : loc:Location.t -> int -> value comp

(** For matching *)
val get_bound : loc:Location.t -> int -> env -> value

(** Add a bound variable with given name to the environment. *)
val add_bound : Name.ident -> value -> 'a comp -> 'a comp

val add_bound_rec :
  (Name.ident * (value -> value comp)) list -> 'a comp -> 'a comp

(** Modify the value bound by a dynamic variable *)
val now : loc:Location.t -> int -> value -> 'a comp -> 'a comp

val top_now : loc:Location.t -> int -> value -> unit toplevel

(** Add a bound variable (for matching). *)
val push_bound : Name.ident -> value -> env -> env

(** [add_free ~loc x (ctx,t) f] generates a fresh atom [y] from identifier [x],
    then it extends [ctx] to [ctx' = ctx, y : t]
    and runs [f ctx' y] in the environment with [x] bound to [ctx' |- y : t].
    NB: This is an effectful computation, as it increases a global counter. *)
val add_free: loc:Location.t -> Name.ident -> Jdg.ty -> (Context.t -> Name.atom -> 'a comp) -> 'a comp

(** [add_free ~loc ?bind x (ctx,t) f] generates a fresh atom [y] from identifier [x],
    then it extends [ctx] to [ctx' = ctx, y : t]
    and runs [f ctx' y] in the environment with
      - [y] marked as abstracting and
      - if [bind] then [x] bound to [ctx' |- y : t] (default behavior).
    NB: This is an effectful computation, as it increases a global counter. *)
val add_abstracting: loc:Location.t -> ?bind:bool -> Name.ident -> Jdg.ty ->
                     (Context.t -> Name.atom -> 'a comp) -> 'a comp

(** Add an operation. *)
val add_operation : loc:Location.t -> Name.ident -> unit toplevel

(** Add a data constructor. *)
val add_data : loc:Location.t -> Name.ident -> unit toplevel

(** Add a constant of a given type to the environment. *)
val add_constant : loc:Location.t -> Name.ident -> Tt.ty -> unit toplevel

(** Add a signature declaration to the environment. *)
val add_signature : loc:Location.t -> Name.signature -> Tt.sig_def -> unit toplevel

(** Add a bound variable with the given name to the environment. *)
val add_topbound : loc:Location.t -> Name.ident -> value -> unit toplevel

val add_topbound_rec : loc:Location.t -> (Name.ident * (value -> value comp)) list -> unit toplevel

(** Add a dynamic variable. *)
val add_dynamic : loc:Location.t -> Name.ident -> value -> unit toplevel

(** Add a top-level handler case to the environment. *)
val add_handle : Name.ident -> (value list * Jdg.ty option,value) closure -> unit toplevel

(** Lookup the current continuation. *)
val continue : loc:Location.t -> value -> value comp

(** Get the printing environment from the monad *)
val lookup_penv : Tt.print_env comp

(** Print free variables in the environment *)
val print_env : (Format.formatter -> unit) toplevel


(** Used to compute command per command *)
type 'a progress

(** runs with empty starting environment not containing declarations used by the kernel *)
val start : 'a toplevel -> 'a progress
val step : 'a progress -> ('a -> 'b toplevel) -> 'b progress
val finish : 'a progress -> 'a

(** Handling *)
val handle_comp : handler -> value comp -> value comp

val top_handle : loc:Location.t -> 'a comp -> 'a toplevel

(** Check whether two values are equal. *)
val equal_value: value -> value -> bool


