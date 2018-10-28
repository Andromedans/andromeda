(** Typing contexts. *)

(** The type of typing contexts.
    A typing context contains information about the current bound variables, declared operations and type definitions as well the current continuation. *)
type t

(** The empty typing context. *)
val empty : t

(** Lookup a bound variable by its De Bruijn index and instantiate its type parameters with fresh metavariables. *)
val lookup_var : Dsyntax.bound -> t -> Mlty.ty

(** Lookup an operation, returning the expected types of its arguments and the type it returns. *)
val lookup_op : Name.operation -> t -> Mlty.ty list * Mlty.ty

(** Lookup an AML constructor, returning the expected types of its arguments and the type it returns. *)
val lookup_aml_constructor : Name.constructor -> t -> Mlty.ty list * Mlty.ty

(** Lookup an TT constructor, returning the expected types of its arguments and the type it returns. *)
val lookup_tt_constructor : Name.constructor -> t -> Mlty.tt_constructor

(** Lookup the continuation, returning the expected type of its argument and the type it returns. *)
val lookup_continuation : t -> Mlty.ty * Mlty.ty

(** Define a new TT constructor. *)
val add_tt_constructor : Name.constructor -> Mlty.tt_constructor -> t -> t

(** Define a new type. The type definition may refer to not-yet-defined types, relying on the caller to add them afterwards. *)
val add_tydef : Name.ident -> Mlty.ty_def -> t -> t

(** Declare a new operation. *)
val add_operation : Name.operation -> Mlty.ty list * Mlty.ty -> t -> t

(** Add a variable of polymorphic type given by the schema. *)
val add_let : Name.ident -> Mlty.ty_schema -> t -> t

(** Creates the context for evaluating the operation handling of [op] *)
val op_cases : Name.operation -> output:Mlty.ty -> t -> Mlty.ty list * t

(** If [x ps] is a type alias for [t] then [unfold ctx x ts] returns [Some] of [t] with the parameters [ps] instantiated with the types [ts], otherwise it returns [None] *)
val unfold : t -> Dsyntax.level -> Mlty.ty list -> Mlty.ty option

(** Produce the set of all metavariables appearing in the context. *)
val gather_known : Substitution.t -> t -> Mlty.MetaSet.t

(** [predefined_type x ts ctx] creates the type [x ts] assuming the type definition for [x] can be found in [ctx]. *)
val predefined_type : Name.ty -> Mlty.ty list -> t -> Mlty.ty

val print_context : t -> unit
