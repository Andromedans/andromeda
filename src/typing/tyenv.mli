(** The full typing environment. *)

(** The type of typing environments.
    An environment is a typing context together with a substitution and unsolved constraints. *)
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

(** Lookup a bound variable by its De Bruijn index and instantiate its type parameters with fresh metavariables. *)
val lookup_var : Rsyntax.bound -> Mlty.ty tyenvM

(** Lookup an operation, returning the expected types of its arguments and the type it returns. *)
val lookup_op : Name.operation -> (Mlty.ty list * Mlty.ty) tyenvM

(** Lookup an AML constructor, returning the expected types of its arguments and the type it returns. *)
val lookup_aml_constructor : Name.constructor -> (Mlty.ty list * Mlty.ty) tyenvM

(** Lookup a TT constructor, returning its expected form. *)
val lookup_tt_constructor : Name.constructor -> Mlty.tt_constructor_ty tyenvM

(** Lookup the continuation, returning the expected type of its argument and the type it returns. *)
val lookup_continuation : (Mlty.ty * Mlty.ty) tyenvM

(** [add_equation ~loc t1 t2] try to unify the actual type [t1] with the expected type
    [t2]. If successful, retry to solve the current unsolved constraints. *)
val add_equation : loc:Location.t -> Mlty.ty -> Mlty.ty -> unit tyenvM

(** [add_application h arg out] checks that a value of type [h] applied to a value of type [arg] will produce a value of type [out].
    Depending on the arguments, it may fail, or create a new unsolved constraint, or solve old ones. *)
val add_application : loc:Location.t -> Mlty.ty -> Mlty.ty -> Mlty.ty -> unit tyenvM

(** Express the given type as a handler type. *)
val as_handler : loc:Location.t -> Mlty.ty -> (Mlty.ty * Mlty.ty) tyenvM

(** Express the given type as a reference type. *)
val as_ref : loc:Location.t -> Mlty.ty -> Mlty.ty tyenvM

(** Express the given type as a dynamic variable type. *)
val as_dynamic : loc:Location.t -> Mlty.ty -> Mlty.ty tyenvM

(** [op_cases op output m] runs [m] with the expected types of the arguments of [op] and
   the continuation having the appropriate type. *)
val op_cases : Name.operation -> output:Mlty.ty -> (Mlty.ty list -> 'a tyenvM) -> 'a tyenvM

(** [predefined_type x ts] creates the type [x ts] assuming the type definition for [x]
    can be found in the environment. *)
val predefined_type : Name.ty -> Mlty.ty list -> Mlty.ty tyenvM

(** Generalize the given type as much as possible in the current environment. *)
val generalize : Mlty.ty -> Mlty.ty_schema tyenvM

(** Check that the given type can be generalized to the given schema in the current
    environment, possibly solving unification problems. *)
val generalizes_to : loc:Location.t -> Mlty.ty -> Mlty.ty_schema -> unit tyenvM

(** Return the given type as a schema without generalizing anything. *)
val ungeneralize : Mlty.ty -> Mlty.ty_schema tyenvM

(** Apply the current substitution to the given schema. *)
(* val normalize_schema : Mlty.ty_schema -> Mlty.ty_schema tyenvM *)

(** Bind a variable with a polymorphic type. NB: if the scope of the variable is local
    then the call to the function should be suitable enclosed by [locally], see above. *)
val add_let : Name.ident -> Mlty.ty_schema -> unit tyenvM

(** [locally m] runs the computation [m] and upon its completetion restores the context.
    This is used to handle locally scoped variables in let bindings and match cases. *)
val locally : 'a tyenvM -> 'a tyenvM

(** [record_vars m] runs the computation [m] and records what variables were added by it, with their types.
    It then returns the list of variables so added by [m], and the original result of [m]. *)
val record_vars : 'a tyenvM -> ((Name.ident * Mlty.ty) list * 'a) tyenvM

(** [locally_add_var x t m] runs the computation [m] in the context extended with the
    variable [x] of type [t]. It removes the variable from the context after [m] is done. *)
val locally_add_var : Name.ident -> Mlty.ty -> 'a tyenvM -> 'a tyenvM

(** [add_var x t m] binds a variable with name [x] and monomorphic type [t]. NB: if the
   scope of the variable is local then you probably want [locally_add_var], or even [locally]. *)
val add_var : Name.ident -> Mlty.ty -> unit tyenvM

(** Define a new type. The type definition may refer to not-yet-defined types, relying on the caller to add them afterwards. *)
val add_tydef : Name.ty -> Mlty.ty_def -> unit tyenvM

(** Declare a new operation. *)
val add_operation : Name.operation -> Mlty.ty list * Mlty.ty -> unit tyenvM
