(** Runtime values and results *)

(* Information about a toplevel declaration *)
type decl =
  | DeclConstant of Tt.ty
  | DeclData of int
  | DeclOperation of int
  | DeclSignature of Tt.sig_def

(** Runtime environment *)
type env

type ('a,'b) closure

(** The values are "finished" or "computed" results. They are inert pieces
    of data. *)
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

(** dynamically scoped environment + operations *)
type 'a result

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

val apply_closure : ('a,'b) closure -> 'a -> 'b result

(** References *)
val mk_ref : value -> value result

val lookup_ref : Store.key -> value result

val update_ref : Store.key -> value -> unit result

(** Monadic primitives *)
val bind: 'a result -> ('a -> 'b result)  -> 'b result

val top_bind : 'a toplevel -> ('a -> 'b toplevel) -> 'b toplevel

(** Catch errors. The state is not changed if the command fails. *)
val catch : (unit -> 'a toplevel) -> ('a,Error.details) Error.res toplevel

val top_return : 'a -> 'a toplevel
val return : 'a -> 'a result

(* XXX why do we need all of these? *)
val top_return_closure : ('a -> 'b result) -> ('a,'b) closure toplevel
val top_mk_closure : (value -> value result) -> value toplevel
val return_closure : (value -> value result) -> value result

val return_term : Jdg.term -> value result
val return_unit : value result

val return_handler :
   (value -> value result) option ->
   (operation_args -> value result) Name.IdentMap.t ->
   (value -> value result) option ->
   value result

val top_fold : ('a -> 'b -> 'a toplevel) -> 'a -> 'b list -> 'a toplevel

(** Pretty-print a value. *)
val print_value : (?max_level:int -> value -> Format.formatter -> unit) result
val print_term : (?max_level:int -> Tt.term -> Format.formatter -> unit) result
val print_ty : (?max_level:int -> Tt.ty -> Format.formatter -> unit) result

val top_print_value : (?max_level:int -> value -> Format.formatter -> unit) toplevel

(** Coerce values *)
val as_term : loc:Location.t -> value -> Jdg.term
val as_closure : loc:Location.t -> value -> (value,value) closure
val as_handler : loc:Location.t -> value -> handler
val as_ref : loc:Location.t -> value -> Store.key
val as_string : loc:Location.t -> value -> string
val as_ident : loc:Location.t -> value -> Name.ident

val as_option : loc:Location.t -> value -> value option
val as_list : loc:Location.t -> value -> value list
val as_sum : loc:Location.t -> value -> (value,value) Tt.sum

(** Wrappers for making tags *)
val from_option : value option -> value
val from_list : value list -> value
val from_sum : (value,value) Tt.sum -> value

val list_nil : value
val list_cons : value -> value list -> value

(** Operations *)
val operation : Name.ident -> ?checking:Jdg.ty -> value list -> value result

val operation_equal : value -> value -> value result

val operation_as_prod : value -> value result
val operation_as_eq : value -> value result
val operation_as_signature : value -> value result

(** Interact with the environment *)

(** Known bound variables *)
val top_bound_names : Name.ident list toplevel

(** Extract the current environment (for desugaring) *)
val top_get_env : env toplevel

(** Extract the current environment (for matching) *)
val get_env : env result

(** Lookup a data constructor. *)
val get_decl : Name.ident -> env -> decl option

(** Lookup an operation *)
val get_operation : Name.ident -> env -> int option

(** Lookup a data constructor *)
val get_data : Name.ident -> env -> int option

(** Lookup a constant. *)
val get_constant : Name.ident -> env -> Tt.ty option

val lookup_constant : loc:Location.t -> Name.ident -> Tt.ty result

(** Lookup a signature definition *)
val get_signature : Name.signature -> env -> Tt.sig_def option

(** Lookup a signature definition, monadically *)
val lookup_signature : loc:Location.t -> Name.ident -> Tt.sig_def result

(** Find a signature with the given labels (in this exact order) *)
val find_signature : loc:Location.t -> Name.label list -> (Name.signature * Tt.sig_def) result

(** Lookup abstracting variables. *)
val lookup_abstracting : Jdg.term list result

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : loc:Location.t -> Syntax.bound -> value result

(** For matching *)
val get_bound : loc:Location.t -> Syntax.bound -> env -> value

(** Add a bound variable with given name to the environment. *)
val add_bound : Name.ident -> value -> 'a result -> 'a result

(** Add a bound variable (for matching). *)
val push_bound : Name.ident -> value -> env -> env

(** [add_free ~loc x t f] generates a fresh atom [y] from identifier [x].
    It then runs [f y] in the environment with [x] bound to [y]. *)
val add_free: loc:Location.t -> Name.ident -> Jdg.ty -> (Context.t -> Name.atom -> 'a result) -> 'a result

(** [add_abstracting ~loc x t] generates a fresh atom [y] from identifier [x] and marks
    it as abstracting (which means we intend to abstract it later).
    It then runs [f y] in the environment with [x] bound to [y]. *)
val add_abstracting: loc:Location.t -> ?bind:bool -> Name.ident -> Jdg.ty ->
                     (Context.t -> Name.atom -> 'a result) -> 'a result

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

(** Simultaenously add bound variables with the given names to the environment.
    Complain if any of the names is already used. *)
val add_topbounds : loc:Location.t -> (Name.ident * value) list -> unit toplevel

(** Add a top-level handler case to the environment. *)
val add_handle : Name.ident -> (value list * Jdg.ty option,value) closure -> unit toplevel

(** Set the continuation for a handler computation. *)
val set_continuation : (value,value) closure -> 'a result -> 'a result

(** Lookup the current continuation. *)
val lookup_continuation : loc:Location.t -> ((value,value) closure) result

(** Add a file to the list of files included. *)
val push_file : string -> unit toplevel

(** Check whether a file has already been included. Files are compared by
  their basenames *)
val included : string -> bool toplevel

(** Get the printing environment from the monad *)
val lookup_penv : Tt.print_env result

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
val handle_result : handler -> value result -> value result

val top_handle : loc:Location.t -> 'a result -> 'a toplevel

(** Check whether two values are equal. *)
val equal_value: value -> value -> bool


