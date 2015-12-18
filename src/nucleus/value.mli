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

module Env : sig

(** Runtime environment *)

type t

(** The empty environment *)
val empty : t

(** List of constants with their arities. *)
val constants : t -> (Name.ident * int) list

(** Known bound variables *)
val bound_names : t -> Name.ident list

(** Variable names already used in the environment *)
val used_names : t -> Name.ident list

(** Lookup a constant. *)
val lookup_constant : Name.ident -> t -> Tt.constsig option

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : loc:Location.t -> Syntax.bound -> t -> value

(** Return all beta hints in the environment *)
val beta_hints : Pattern.hint_key -> t -> Pattern.beta_hint list

(** Return all eta hints in the environment *)
val eta_hints : Pattern.hint_key -> t -> Pattern.eta_hint list

(** Return all general hints in the environment *)
val general_hints : Pattern.general_key -> t -> Pattern.general_hint list

(** Return all general hints in the environment *)
val inhabit_hints : Pattern.hint_key -> t -> Pattern.inhabit_hint list

(** [add_fresh ~loc env x t] generates a fresh atom [y] from identifier [x]. Return [y] and
    the environment updated with [x] bound to [y:t]. *)
val add_fresh: loc:Location.t -> t -> Name.ident -> Judgement.ty -> Context.t * Name.atom * t

(** Add a constant of a given signature to the environment.
    Fails if the constant is already bound. *)
val add_constant : loc:Location.t -> Name.ident -> Tt.constsig -> t -> t

(** Add an untagged beta hint to the environment. *)
val add_beta : Pattern.hint_key * Pattern.beta_hint -> t -> t

(** Add beta hints to the environment. *)
val add_betas : (string list * (Pattern.hint_key * Pattern.beta_hint)) list -> t -> t

(** Add eta hints to the environment. *)
val add_etas : (string list * (Pattern.hint_key * Pattern.eta_hint)) list -> t -> t

(** Add general hints to the environment. *)
val add_generals :
  (string list *
   (Pattern.general_key * Pattern.general_hint)) list ->
  t -> t

(** Add an inhabit hint to the environment. *)
val add_inhabits : (string list * (Pattern.hint_key * Pattern.inhabit_hint)) list -> t -> t

(** Remove all hints with one of the given tags *)
val unhint : loc:Location.t -> string list -> t -> t

(** Add a bound variable with given name to the environment. *)
val add_bound : Name.ident -> value -> t -> t

(** Add a top-level handler case to the environment. *)
val add_handle : string -> (Name.ident * Syntax.comp) -> t -> t

(** Lookup the top-level handler for the given operation, if any. *)
val lookup_handle : string -> t -> (Name.ident * Syntax.comp) option

(** Set the continuation for a handler computation. *)
val set_continuation : value -> t -> t

(** Lookup the current continuation. *)
val lookup_continuation : t -> value option

(** Add a file to the list of files included. *)
val add_file : string -> t -> t

(** Check whether a file has already been included. Files are compared by
    their basenames *)
val included : string -> t -> bool

(** Print free variables in the environment *)
val print : t -> Format.formatter -> unit

(** Match a value against a pattern and extend the environment with the
    matched pattern variables. *)
val match_pattern : t -> Name.ident list -> Syntax.pattern -> value -> t option

end (* [sig Env] *)
