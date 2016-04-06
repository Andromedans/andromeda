
type constrain =
  | AppConstraint of Location.t * Mlty.ty * Mlty.ty * Mlty.ty

type generalizable =
  | Generalizable
  | Ungeneralizable

val generalizable : Syntax.comp -> generalizable

type t

val empty : t

val lookup_var : Syntax.bound -> t -> Mlty.ty

val lookup_op : Name.operation -> t -> Mlty.ty list * Mlty.ty

val lookup_constructor : Name.constructor -> t -> Mlty.ty list * Mlty.ty

val lookup_continuation : t -> Mlty.ty * Mlty.ty

val add_var : Name.ident -> Mlty.ty_schema -> t -> t

val add_tydef : Name.ident -> Mlty.ty_def -> t -> t

val add_operation : Name.operation -> Mlty.ty list * Mlty.ty -> t -> t

val add_lets : (Name.ident * generalizable * Mlty.ty) list -> Mlty.MetaSet.t -> Substitution.t -> t -> t

(** Creates the context for evaluating the operation handling of [op] *)
val op_cases : Name.operation -> output:Mlty.ty -> t -> Mlty.ty list * t

val unfold : t -> Syntax.level -> Mlty.ty list -> Mlty.ty option

val gather_known : t -> Mlty.MetaSet.t

(** Make an instance of a predefined type. Must be used with the correct arity. *)
val predefined_type : Name.ty -> Mlty.ty list -> t -> Mlty.ty

