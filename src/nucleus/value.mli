(** Runtime values and results *)

(* Information about a toplevel declaration *)
type decl =
  | Constant of Tt.constsig
  | Data of int
  | Operation of int

(** Runtime environment *)
type env

type dynamic

(** The values are "finished" or "computed" results. They are inert pieces
    of data.

    At the moment the only kind of value is a pair [(e,t)] where [e] is a
    term and [t] is a type. Such a value (in a given context [ctx]) indicates
    that the judgement [ctx |- e : t] is derivable. *)
type value =
  | Term of Judgement.term
  | Ty of Judgement.ty
  | Closure of value closure
  | Handler of handler
  | Tag of Name.ident * value list

and 'a closure

(** A result of computation at the moment is necessarily just a pure value
    because we do not have any operations in the language. But when we do,
    they will be results as well (and then handlers will handle them). *)
and 'a result =
  | Return of 'a
  | Operation of Name.ident * value * dynamic * 'a closure

and handler = {
  handler_val: value closure option;
  handler_ops: (Name.ident * (dynamic -> value -> value closure -> value result)) list;
  handler_finally: value closure option;
}

val mk_closure' : env -> (env -> value -> value result) -> value closure
val mk_closure : env -> (env -> value -> value result) -> value
val apply_closure : env -> 'a closure -> value -> 'a result

val as_term : loc:Location.t -> value -> Judgement.term
val as_ty : loc:Location.t -> value -> Judgement.ty
val as_closure : loc:Location.t -> value -> value closure
val as_handler : loc:Location.t -> value -> handler


(** Names and arities of predefined data constructors *)
val predefined_tags : (Name.ident * int) list

(** Wrappers for making tags *)
val from_option : value option -> value
val from_pair : value * value -> value
val from_unit : unit -> value
val from_list : value list -> value

(** Convert tags to ocaml types *)
val as_option : loc:Location.t -> value -> value option

val mk_tag : Name.ident -> value list -> value

val return : 'a -> 'a result
val return_term : Judgement.term -> value result
val return_ty : Judgement.ty -> value result
val return_closure : env -> (env -> value -> value result) -> value result

val return_handler : env ->
   (env -> value -> value result) option ->
   (Name.ident * (env -> value -> (value closure -> value result))) list ->
   (env -> value -> value result) option ->
   value result

val bind: 'a result -> ('a -> 'b result)  -> 'b result

val perform : Name.ident -> env -> value list -> value result

(** Pretty-print a value. *)
val print_value : ?max_level:int -> Name.ident list -> value -> Format.formatter -> unit

val print_value_key : value -> Format.formatter -> unit

(** Check that a result is a value and return it, or complain. *)
val to_value : loc:Location.t -> 'a result -> 'a

(** Check whether two values are equal. *)
val equal_value: value -> value -> bool

(** [mk_abstractable ctx xs] prepares context [ctx] for abstracting atoms [xs].
    It returns a context [ctx'], atoms [ys] and terms [es],
    with [ctx'] the context where the atoms [ys] blocking abstraction in [ctx] have been instantiated  by [es]. *)
val mk_abstractable : loc:Location.t -> env -> Context.t -> Name.atom list ->
  (Context.t * Name.atom list * Tt.term list) result

(** [context_abstract ctx xs ts] computes [mk_abstractable ctx xs],
    and abstracts the result by [xs] and [ts]. *)
val context_abstract : loc:Location.t -> env -> Context.t -> Name.atom list -> Tt.ty list ->
  (Context.t * Name.atom list * Tt.term list) result

module Env : sig
  type t = env

  (** The empty environment *)
  val empty : env

  (** Known bound variables *)
  val bound_names : env -> Name.ident list

  (** Variable names already used in the environment *)
  val used_names : env -> Name.ident list

  (** Lookup a data constructor. *)
  val lookup_decl : Name.ident -> env -> decl option

  (** Lookup a constant. *)
  val lookup_constant : Name.ident -> env -> Tt.constsig option

  (** Lookup abstracting variables. *)
  val lookup_abstracting : env -> Judgement.term list

  (** Lookup a free variable by its de Bruijn index *)
  val lookup_bound : loc:Location.t -> Syntax.bound -> env -> value

  (** [add_free ~loc env x t] generates a fresh atom [y] from identifier [x]. Return [y] and
    the environment updated with [x] bound to [y:t]. *)
  val add_free: loc:Location.t -> env -> Name.ident -> Judgement.ty -> Context.t * Name.atom * env

  (** [add_abstracting ~loc env x t] generates a fresh atom [y] from identifier [x] and marks
      it as abstracting (which means we intend to abstract it later). Return [y] and
      the environment updated with [x] bound to [y:t]. *)
  val add_abstracting: loc:Location.t -> env ->
                       Name.ident -> Judgement.ty -> Context.t * Name.atom * env

  (** Add an operation with the given arity.
      It fails if the operation is already declared. *)
  val add_operation : loc:Location.t -> Name.ident -> int -> env -> env

  (** Add a data constructor with the given arity.
      It fails if the constructor is already declared. *)
  val add_data : loc:Location.t -> Name.ident -> int -> env -> env

  (** Add a constant of a given signature to the environment.
    Fails if the constant is already declared. *)
  val add_constant : loc:Location.t -> Name.ident -> Tt.constsig -> env -> env

  (** Add a bound variable with given name to the environment. *)
  val add_bound : Name.ident -> value -> env -> env

  (** Add a top-level handler case to the environment. *)
  val add_handle : Name.ident -> (Name.ident * Syntax.comp) -> env -> env

  (** Lookup the top-level handler for the given operation, if any. *)
  val lookup_handle : Name.ident -> env -> (Name.ident * Syntax.comp) option

  (** Set the continuation for a handler computation. *)
  val set_continuation : value closure -> env -> env

  (** Set the dynamic part of an environment. *)
  val set_dynamic : t -> dynamic -> t

  (** Lookup the current continuation. *)
  val lookup_continuation : env -> (value closure) option

  (** Add a file to the list of files included. *)
  val add_file : string -> env -> env

  (** Check whether a file has already been included. Files are compared by
    their basenames *)
  val included : string -> env -> bool

  (** Print free variables in the environment *)
  val print : env -> Format.formatter -> unit

  (** Match a value against a pattern and extend the environment with the
    matched pattern variables. *)
  val match_pattern : env -> Name.ident list -> Syntax.pattern -> value -> env option

end (* [sig Env] *)
