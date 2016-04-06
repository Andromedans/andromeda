
type constrain =
  | AppConstraint of Location.t * Amltype.ty * Amltype.ty * Amltype.ty

type generalizable =
  | Generalizable
  | Ungeneralizable

val generalizable : Syntax.comp -> generalizable

type t

val empty : t

val lookup_var : Syntax.bound -> t -> Amltype.ty

val lookup_op : Name.operation -> t -> Amltype.ty list * Amltype.ty

val lookup_constructor : Name.constructor -> t -> Amltype.ty list * Amltype.ty

val lookup_continuation : t -> Amltype.ty * Amltype.ty

val add_var : Name.ident -> Amltype.ty_schema -> t -> t

val add_tydef : Name.ident -> Amltype.ty_def -> t -> t

val add_operation : Name.operation -> Amltype.ty list * Amltype.ty -> t -> t

val add_lets : (Name.ident * generalizable * Amltype.ty) list -> Amltype.MetaSet.t -> Substitution.t -> t -> t

(** Creates the context for evaluating the operation handling of [op] *)
val op_cases : Name.operation -> output:Amltype.ty -> t -> Amltype.ty list * t

val unfold : t -> Syntax.level -> Amltype.ty list -> Amltype.ty option

val gather_known : t -> Amltype.MetaSet.t

(** Make an instance of a predefined type. Must be used with the correct arity. *)
val predefined_type : Name.ty -> Amltype.ty list -> t -> Amltype.ty

