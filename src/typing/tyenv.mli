(** The full typing environment. *)

(** The type of typing environments: a typing context together with a
    substitution and unsolved constraints. *)
type t

(** The empty typing environment. *)
val empty : t

(** A monadic type to make environment management easier while checking computations. *)
type 'a tyenvM

(** Monadic return. *)
val return : 'a -> 'a tyenvM

(** Monadic bind. *)
val (>>=) : 'a tyenvM -> ('a -> 'b tyenvM) -> 'b tyenvM

val run : t -> 'a tyenvM -> t * 'a

(** Return the typing context at the current stage. Only exposed for use with
   [generalize] and [generalizes_to]. The context will likely become invalid at
   a later point and should be used only with the greatest care. *)
val get_context : Context.t tyenvM

(** Lookup a bound variable by its De Bruijn index and instantiate its type parameters with fresh metavariables. *)
val lookup_bound : Path.index -> Mlty.ty tyenvM

(** Lookup a bound variable by its De Bruijn index and instantiate its type parameters with fresh metavariables. *)
val lookup_ml_value : Path.t -> Mlty.ty tyenvM

(** Lookup an operation, returning the expected types of its arguments and the type it returns. *)
val lookup_ml_operation : Path.t -> (Ident.t * (Mlty.ty list * Mlty.ty)) tyenvM

(** Lookup an ML constructor, returning the expected types of its arguments and the type it returns. *)
val lookup_ml_constructor : Path.ml_constructor -> (Mlty.ty list * Mlty.ty) tyenvM

(** Lookup a TT constructor, returning its expected form. *)
val lookup_tt_constructor : Path.t -> (Ident.t * Mlty.tt_constructor) tyenvM

(** Lookup the continuation, returning the expected type of its argument and the type it returns. *)
val lookup_continuation : (Mlty.ty * Mlty.ty) tyenvM

(** Add a TT constructor to the typing context, globally forever. *)
val add_tt_constructor : Name.t -> Mlty.tt_constructor -> unit tyenvM

(** [add_equation ~loc t1 t2] try to unify the actual type [t1] with the expected type
    [t2]. If successful, retry to solve the current unsolved constraints. *)
val add_equation : loc:Location.t -> Mlty.ty -> Mlty.ty -> unit tyenvM

(** Express the given type as a handler type. *)
val as_handler : loc:Location.t -> Mlty.ty -> (Mlty.ty * Mlty.ty) tyenvM

(** Express the given type as a reference type. *)
val as_ref : loc:Location.t -> Mlty.ty -> Mlty.ty tyenvM

(** Express the given type as a dynamic variable type. *)
val as_dynamic : loc:Location.t -> Mlty.ty -> Mlty.ty tyenvM

(** [op_cases op output m] runs [m] with the expected types of the arguments of [op] and
   the continuation having the appropriate type. *)
val op_cases : Path.t -> output:Mlty.ty -> (Mlty.ty list -> 'a tyenvM) -> 'a tyenvM

(** Generalize the given type as much as possible in the current environment,
    but using only [known_context] as typing context, possibly solving
    unification problems. If [known_context] is not provided, use the one from
    the current typechecking environment. *)
val generalize : known_context:Context.t -> Mlty.ty -> Mlty.ty_schema tyenvM

(** Check that the given type can be generalized to the given schema in the
    current environment but using only [known_context] as typing context,
    possibly solving unification problems. If [known_context] is not provided,
    use the one from the current typechecking environment. *)
val generalizes_to
  : loc:Location.t -> known_context:Context.t -> Mlty.ty -> Mlty.ty_schema -> unit tyenvM

(** Return the given type as a schema without generalizing anything. *)
val ungeneralize : Mlty.ty -> Mlty.ty_schema tyenvM

(** Apply the current substitution to the given schema. *)
(* val normalize_schema : Mlty.ty_schema -> Mlty.ty_schema tyenvM *)

(** Bind a variable with a polymorphic type. NB: if the scope of the variable is local
    then the call to the function should be suitable enclosed by [locally], see above. *)
val add_ml_value : Name.t -> Mlty.ty_schema -> unit tyenvM

(** [locally m] runs the computation [m] and upon its completetion restores the context.
    This is used to handle locally scoped variables in let bindings and match cases. *)
val locally : 'a tyenvM -> 'a tyenvM

(** [record_ml_value x t] records the fact that variable [x] of type [t] was found.
    Later the so recorded variables are reported by [record_vars]. This is used
    for collecting bound variables in match cases and let bindings. *)
val record_ml_value : Name.t -> Mlty.ty -> unit tyenvM

(** [record_ml_values m] runs the computation [m] and records what variables were registered
   using [record_var]. It then returns the list of variables so added by [m], and the
   original result of [m]. This is used for collecting bound variables in match cases
   and let bindings. *)
val record_ml_values : 'a tyenvM -> ((Name.t * Mlty.ty) list * 'a) tyenvM

(** [locally_add_var x t m] runs the computation [m] in the context extended with the
    variable [x] of type [t]. It removes the variable from the context after [m] is done. *)
val locally_add_ml_value : Name.t -> Mlty.ty -> 'a tyenvM -> 'a tyenvM

(** [add_ml_value x t m] binds a variable with name [x] and monomorphic type [t]. NB: if the
   scope of the variable is local then you probably want [locally_add_var], or even [locally]. *)
(* val add_ml_value : Name.t -> Mlty.ty -> unit tyenvM *)

(** Define a new type. The type definition may refer to not-yet-defined types, relying on the caller to add them afterwards. *)
val add_ml_type : Name.t -> Mlty.ty_def -> unit tyenvM

(** Declare a new operation. *)
val add_ml_operation : Name.t -> Mlty.ty list * Mlty.ty -> unit tyenvM

(** Print the typing context (useful for debugging) *)
val print_context : t -> unit
