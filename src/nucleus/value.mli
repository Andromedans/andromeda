(** Runtime values and computations *)

(* Information about a toplevel declaration *)
type decl =
  | DeclConstant of Tt.ty
  | DeclData of int
  | DeclOperation of int
  | DeclSignature of Tt.sig_def

(** Runtime environment *)
type env

type ('a,'b) closure

(** The values are "finished" or "computed". They are inert pieces of data. *)
type value = private
  | Term of Jdg.term
  | Closure of (value,value) closure
  | Handler of handler
  | Tag of Name.ident * value list
  | List of value list
  | Tuple of value list
  | Ref of Store.key
  | String of string (** NB: strings are opaque to the user, ie not lists *)
  | Ident of Name.ident

and operation_args = { args : value list; checking : Jdg.ty option; cont : (value,value) closure }

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (operation_args, value) closure Name.IdentMap.t;
  handler_finally: (value,value) closure option;
}

(** computations provide a dynamically scoped environment and operations *)
type 'a comp

(** state environment, no operations *)
type 'a toplevel

(** a descriptive name of a value, e.g. the name of [Handler _] is ["a handler"] *)
val name_of : value -> string

(** Make values *)
val mk_term : Jdg.term -> value
val mk_handler : handler -> value
val mk_tag : Name.ident -> value list -> value
val mk_tuple : value list -> value
val mk_string : string -> value
val mk_ident : Name.ident -> value

val mk_list : value list -> value
val list_nil : value
val list_cons : value -> value list -> value

val apply_closure : ('a,'b) closure -> 'a -> 'b comp

(** References *)
val mk_ref : value -> value comp

val lookup_ref : Store.key -> value comp

val update_ref : Store.key -> value -> unit comp

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
val print_value : (?max_level:int -> value -> Format.formatter -> unit) comp
val print_term : (?max_level:int -> Tt.term -> Format.formatter -> unit) comp
val print_ty : (?max_level:int -> Tt.ty -> Format.formatter -> unit) comp

val top_print_value : (?max_level:int -> value -> Format.formatter -> unit) toplevel

(** Coerce values *)
val as_term : loc:Location.t -> value -> Jdg.term
val as_closure : loc:Location.t -> value -> (value,value) closure
val as_handler : loc:Location.t -> value -> handler
val as_ref : loc:Location.t -> value -> Store.key
val as_string : loc:Location.t -> value -> string
val as_ident : loc:Location.t -> value -> Name.ident
val as_list : loc:Location.t -> value -> value list

(** Wrappers for making tags *)
val from_option : value option -> value
val as_option : loc:Location.t -> value -> value option

val from_sum : (value,value) Tt.sum -> value
val as_sum : loc:Location.t -> value -> (value,value) Tt.sum

(** Operations *)
val operation : Name.ident -> ?checking:Jdg.ty -> value list -> value comp

val operation_equal : value -> value -> value comp

val operation_as_prod : value -> value comp
val operation_as_eq : value -> value comp
val operation_as_signature : value -> value comp

(** Interact with the environment *)

(** Known bound variables *)
val top_bound_names : Name.ident list toplevel

(** Extract the current environment (for desugaring) *)
val top_get_env : env toplevel

(** Extract the current environment (for matching) *)
val get_env : env comp

(** Lookup a data constructor. *)
val get_decl : Name.ident -> env -> decl option

(** Lookup an operation *)
val get_operation : Name.ident -> env -> int option

(** Lookup a data constructor *)
val get_data : Name.ident -> env -> int option

(** Lookup a constant. *)
val get_constant : Name.ident -> env -> Tt.ty option

val lookup_constant : loc:Location.t -> Name.ident -> Tt.ty comp

(** Lookup a signature definition *)
val get_signature : Name.signature -> env -> Tt.sig_def option

(** Lookup a signature definition, monadically *)
val lookup_signature : loc:Location.t -> Name.ident -> Tt.sig_def comp

(** Find a signature with the given labels (in this exact order) *)
val find_signature : loc:Location.t -> Name.label list -> (Name.signature * Tt.sig_def) comp

(** Lookup abstracting variables. *)
val lookup_abstracting : Jdg.term list comp

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : loc:Location.t -> Syntax.bound -> value comp

(** For matching *)
val get_bound : loc:Location.t -> Syntax.bound -> env -> value

(** Add a bound variable with given name to the environment. *)
val add_bound : Name.ident -> value -> 'a comp -> 'a comp

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

(** Add an operation with the given arity.
    It fails if the operation is already declared. *)
val add_operation : loc:Location.t -> Name.ident -> int -> unit toplevel

(** Add a data constructor with the given arity.
    It fails if the constructor is already declared. *)
val add_data : loc:Location.t -> Name.ident -> int -> unit toplevel

(** Add a constant of a given type to the environment.
  Fails if the constant is already declared. *)
val add_constant : loc:Location.t -> Name.ident -> Tt.ty -> unit toplevel

(** Add a signature declaration to the environment.
  Fails if the signature is already declared. *)
val add_signature : loc:Location.t -> Name.signature -> Tt.sig_def -> unit toplevel

(** Add a bound variable with the given name to the environment.
    Complain if then name is already used. *)
val add_topbound : loc:Location.t -> Name.ident -> value -> unit toplevel

(** Add a top-level handler case to the environment. *)
val add_handle : Name.ident -> (value list * Jdg.ty option,value) closure -> unit toplevel

(** Set the continuation for a handler computation. *)
val set_continuation : (value,value) closure -> 'a comp -> 'a comp

(** Lookup the current continuation. *)
val lookup_continuation : loc:Location.t -> ((value,value) closure) comp

(** Add a file to the list of files included. *)
val push_file : string -> unit toplevel

(** Check whether a file has already been included. Files are compared by
  their basenames *)
val included : string -> bool toplevel

(** Get the printing environment from the monad *)
val lookup_penv : Tt.print_env comp

(** Print free variables in the environment *)
val print_env : (Format.formatter -> unit) toplevel

(** runs with starting environment already containing declarations used by the kernel *)
val run : 'a toplevel -> 'a

(** Used to compute command per command *)
type 'a progress

val initial : 'a toplevel -> 'a progress
val progress : 'a progress -> ('a -> 'b toplevel) -> 'b progress
val finish : 'a progress -> 'a

(** Handling *)
val handle_comp : handler -> value comp -> value comp

val top_handle : loc:Location.t -> 'a comp -> 'a toplevel

(** Check whether two values are equal. *)
val equal_value: value -> value -> bool


