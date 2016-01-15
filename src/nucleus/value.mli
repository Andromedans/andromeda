(** Runtime values and results *)

(* Information about a toplevel declaration *)
type decl =
  | Constant of Tt.constsig
  | Data of int
  | Operation of int

(** Runtime environment *)
type env

type ('a,'b) closure

(** The values are "finished" or "computed" results. They are inert pieces
    of data. *)
type value = private
  | Term of Judgement.term
  | Ty of Judgement.ty
  | Closure of (value,value) closure
  | Handler of handler
  | Tag of Name.ident * value list
  | List of value list
  | Ref of Store.key
  | String of string (** NB: strings are opaque to the user, ie not lists *)

and handler = {
  handler_val: (value,value) closure option;
  handler_ops: (value list * (value,value) closure, value) closure Name.IdentMap.t;
  handler_finally: (value,value) closure option;
}

(** dynamically scoped environment + operations *)
type 'a result

(** state environment, no operations *)
type 'a toplevel

(** a descriptive name of a value, e.g. the name of [Handler _] is ["a handler"] *)
val name_of : value -> string

(** Make values *)
val mk_term : Judgement.term -> value
val mk_ty : Judgement.ty -> value
val mk_handler : handler -> value
val mk_tag : Name.ident -> value list -> value
val mk_string : string -> value

val mk_closure' : ('a -> 'b result) -> ('a,'b) closure toplevel

val apply_closure : ('a,'b) closure -> 'a -> 'b result

(** References *)
val mk_ref : value -> value result

val lookup_ref : Store.key -> value result

val update_ref : Store.key -> value -> unit result

(** Monadic primitives *)
val bind: 'a result -> ('a -> 'b result)  -> 'b result

val top_bind : 'a toplevel -> ('a -> 'b toplevel) -> 'b toplevel

(** Catch errors. The state is not changed if the command fails. *)
val catch : 'a toplevel -> ('a,Error.details) Error.res toplevel

val top_return : 'a -> 'a toplevel
val return : 'a -> 'a result

val return_term : Judgement.term -> value result
val return_ty : Judgement.ty -> value result
val return_closure : (value -> value result) -> value result
val return_unit : value result

val return_handler :
   (value -> value result) option ->
   (value list * (value,value) closure -> value result) Name.IdentMap.t ->
   (value -> value result) option ->
   value result


(** Pretty-print a value. *)
val print_value : (?max_level:int -> value -> Format.formatter -> unit) result
val print_term : (?max_level:int -> Tt.term -> Format.formatter -> unit) result
val print_ty : (?max_level:int -> Tt.ty -> Format.formatter -> unit) result

val top_print_value : (?max_level:int -> value -> Format.formatter -> unit) toplevel

(** Coerce values *)
val as_term : loc:Location.t -> value -> Judgement.term
val as_ty : loc:Location.t -> value -> Judgement.ty
val as_closure : loc:Location.t -> value -> (value,value) closure
val as_handler : loc:Location.t -> value -> handler
val as_ref : loc:Location.t -> value -> Store.key
val as_string : loc:Location.t -> value -> string

val as_option : loc:Location.t -> value -> value option
val as_list : loc:Location.t -> value -> value list

(** Wrappers for making tags *)
val from_option : value option -> value
val from_pair : value * value -> value
val from_list : value list -> value

val list_nil : value
val list_cons : value -> value list -> value

(** Operations *)
val perform : Name.ident -> value list -> value result

val perform_equal : value -> value -> value result

val perform_abstract : value -> value -> value result

val perform_as_prod : value -> value result
val perform_as_eq : value -> value result
val perform_as_signature : value -> value result

(** Interact with the environment *)

(** Known bound variables *)
val top_bound_names : Name.ident list toplevel

(** Extract the current environment (for desugaring) *)
val top_get_env : env toplevel

(** Extract the current environment (for matching) *)
val get_env : env result

(** Lookup a data constructor. *)
val lookup_decl : Name.ident -> env -> decl option

(** Lookup an operation *)
val lookup_operation : Name.ident -> env -> int option

(** Lookup a data constructor *)
val lookup_data : Name.ident -> env -> int option

(** Lookup a constant. *)
val lookup_constant : Name.ident -> Tt.constsig option result

(** Lookup a constant in desugar mode *)
val get_constant :  Name.ident -> env -> Tt.constsig option

(** Lookup abstracting variables. *)
val lookup_abstracting : Judgement.term list result

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
val add_free: loc:Location.t -> Name.ident -> Judgement.ty -> (Context.t -> Name.atom -> 'a result) -> 'a result

(** [add_abstracting ~loc x t] generates a fresh atom [y] from identifier [x] and marks
    it as abstracting (which means we intend to abstract it later).
    It then runs [f y] in the environment with [x] bound to [y]. *)
val add_abstracting: loc:Location.t -> Name.ident -> Judgement.ty ->
                     (Context.t -> Name.atom -> 'a result) -> 'a result

(** Add an operation with the given arity.
    It fails if the operation is already declared. *)
val add_operation : loc:Location.t -> Name.ident -> int -> unit toplevel

(** Add a data constructor with the given arity.
    It fails if the constructor is already declared. *)
val add_data : loc:Location.t -> Name.ident -> int -> unit toplevel

(** Add a constant of a given signature to the environment.
  Fails if the constant is already declared. *)
val add_constant : loc:Location.t -> Name.ident -> Tt.constsig -> unit toplevel

(** Add a bound variable with the given name to the environment.
    Complain if then name is already used. *)
val add_topbound : loc:Location.t -> Name.ident -> value -> unit toplevel

(** Add a top-level handler case to the environment. *)
val add_handle : Name.ident -> (value list,value) closure -> unit toplevel

(** Set the continuation for a handler computation. *)
val set_continuation : (value,value) closure -> 'a result -> 'a result

(** Lookup the current continuation. *)
val lookup_continuation : ((value,value) closure) option result

(** Add a file to the list of files included. *)
val push_file : string -> unit toplevel

(** Check whether a file has already been included. Files are compared by
  their basenames *)
val included : string -> bool toplevel

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


