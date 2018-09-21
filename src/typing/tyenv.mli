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

(** Lookup a bound variable by its De Bruijn index and instantiate its type parameters with fresh metavariables. *)
val lookup_var : Rsyntax.bound -> Mlty.ty tyenvM

(** Lookup an operation, returning the expected types of its arguments and the type it returns. *)
val lookup_op : Name.operation -> (Mlty.ty list * Mlty.ty) tyenvM

(** Lookup an AML constructor, returning the expected types of its arguments and the type it returns. *)
val lookup_aml_constructor : Name.constructor -> (Mlty.ty list * Mlty.ty) tyenvM

(** Lookup the continuation, returning the expected type of its argument and the type it returns. *)
val lookup_continuation : (Mlty.ty * Mlty.ty) tyenvM

(** [add_var x t m] binds a variable with name [x] and monomorphic type [t] while computing in [m]. *)
val add_var : Name.ident -> Mlty.ty -> 'a tyenvM -> 'a tyenvM

(** Try to unify the given types. If successful, retry to solve the current unsolved constraints. *)
val add_equation : loc:Location.t -> Mlty.ty -> Mlty.ty -> unit tyenvM

(** [add_application h arg out] checks that a value of type [h] applied to a value of type [arg] will produce a value of type [out].
    Depending on the arguments, it may fail, or create a new unsolved constraint, or solve old ones. *)
val add_application : loc:Location.t -> Mlty.ty -> Mlty.ty -> Mlty.ty -> unit tyenvM

(** Bind a variable with a polymorphic type. *)
val add_let : Name.ident -> Mlty.ty_schema -> 'a tyenvM -> 'a tyenvM

(** Express the given type as a handler type. *)
val as_handler : loc:Location.t -> Mlty.ty -> (Mlty.ty * Mlty.ty) tyenvM

(** Express the given type as a reference type. *)
val as_ref : loc:Location.t -> Mlty.ty -> Mlty.ty tyenvM

(** Express the given type as a dynamic variable type. *)
val as_dynamic : loc:Location.t -> Mlty.ty -> Mlty.ty tyenvM

(** [op_cases op output m] runs [m] with the expected types of the arguments of [op] and the continuation being from the output type of [op] to [output]. *)
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

(** Toplevel functionality *)

(** Run the given computation with the given environment, outputting the modified environment and the result of the computation. *)
val at_toplevel : t -> 'a tyenvM -> t * 'a

(** Define a new type. The type definition may refer to not-yet-defined types, relying on the caller to add them afterwards. *)
val topadd_tydef : Name.ty -> Mlty.ty_def -> t -> t

(** Declare a new operation. *)
val topadd_operation : Name.operation -> Mlty.ty list * Mlty.ty -> t -> t

(** Add a variable with polymorphic type in the environment. *)
val topadd_let : Name.ty -> Mlty.ty_schema -> t -> t
