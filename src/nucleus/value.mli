(** Runtime values and results *)

(** The values are "finished" or "computed" results. They are inert pieces
    of data.

    At the moment the only kind of value is a pair [(e,t)] where [e] is a
    term and [t] is a type. Such a value (in a given context [ctx]) indicates
    that the judgement [ctx |- e : t] is derivable. *)
type value =
  | Term of Judgement.term
  | Ty of Judgement.ty
  | Closure of closure
  | Handler of handler
  | Tag of Name.ident * value list

 and closure = value -> value result

(** A result of computation at the moment is necessarily just a pure value
    because we do not have any operations in the language. But when we do,
    they will be results as well (and then handlers will handle them). *)
and 'a result =
  | Return of 'a
  | Operation of string * value * (value -> 'a result)

and handler = {
  handler_val: closure option;
  handler_ops: (string * (value -> value -> value result)) list;
  handler_finally: closure option;
}

val as_term : loc:Location.t -> value -> Judgement.term
val as_ty : loc:Location.t -> value -> Judgement.ty
val as_closure : loc:Location.t -> value -> closure
val as_handler : loc:Location.t -> value -> handler

(** Convert tags to ocaml types *)
val as_option : loc:Location.t -> value -> value option

val return : 'a -> 'a result
val return_term : Judgement.term -> value result
val return_ty : Judgement.ty -> value result

val bind: 'a result -> ('a -> 'b result)  -> 'b result

val operate : string -> value -> value result

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
val mk_abstractable : loc:Location.t -> Context.t -> Name.atom list ->
  (Context.t * Name.atom list * Tt.term list) result

(** [context_abstract ctx xs ts] computes [mk_abstractable ctx xs],
    and abstracts the result by [xs] and [ts]. *)
val context_abstract : loc:Location.t -> Context.t -> Name.atom list -> Tt.ty list ->
  (Context.t * Name.atom list * Tt.term list) result

