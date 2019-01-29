(** Typing contexts. *)

(** The type of typing contexts. A typing context contains information about the
   current bound variables, declared operations and type definitions as well the
   current continuation. *)
type t

(** The empty typing context. *)
val empty : t

(** Lookup the type of a bound variable by its De Bruijn index and instantiate
   its type parameters with fresh metavariables. *)
val lookup_bound : Path.index -> t -> Mlty.ty

(** Lookup the identifier of a defined type. *)
val lookup_ml_type_id : Path.t -> t -> Ident.t

(** Lookup the type of a named value by its path, and instantiate its type
   parameters with fresh metavariables. *)
val lookup_ml_value : Path.t -> t -> Mlty.ty

(** Lookup the type of an operation. *)
val lookup_ml_operation : Path.t -> t -> Ident.t * (Mlty.ty list * Mlty.ty)

(** Lookup the type of an ML constructor. *)
val lookup_ml_constructor : Path.ml_constructor -> t -> Mlty.ty list * Mlty.ty

(** Lookup the (M)L type of a TT constructor. *)
val lookup_tt_constructor : Path.t -> t -> Ident.t * Mlty.tt_constructor

(** Lookup the type of the current continuation. *)
val lookup_continuation : t -> Mlty.ty * Mlty.ty

(** Declare a new TT constructor. *)
val add_tt_constructor : Name.t -> Mlty.tt_constructor -> t -> t

(** Define a new type. The type definition may refer to not-yet-defined types, relying on the caller to add them afterwards. *)
val add_ml_type : Name.t -> Mlty.ty_def -> t -> t

(** Declare a new operation. *)
val add_ml_operation : Name.t -> Mlty.ty list * Mlty.ty -> t -> t

(** Add a variable of polymorphic type given by the schema. *)
val add_ml_value : Name.t -> Mlty.ty_schema -> t -> t

(** Creates the context for evaluating the operation handling of [op] *)
val op_cases : Path.t -> output:Mlty.ty -> t -> Ident.t * Mlty.ty list * t

(** Start processing a fresh current module *)
val push_ml_module : t -> t

(** Stop processing the current module *)
val pop_ml_module : t -> t

(** If [x ps] is a type alias for [t] then [unfold ctx x ts] returns [Some] of [t] with the parameters [ps] instantiated with the types [ts], otherwise it returns [None] *)
val unfold : t -> Path.t -> Mlty.ty list -> Mlty.ty option

(** Produce the set of all metavariables appearing in the context. *)
val gather_known : Substitution.t -> t -> Mlty.MetaSet.t
