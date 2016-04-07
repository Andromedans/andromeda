type t

val empty : t

type 'a tyenvM

val return : 'a -> 'a tyenvM

val (>>=) : 'a tyenvM -> ('a -> 'b tyenvM) -> 'b tyenvM

val lookup_var : Syntax.bound -> Mlty.ty tyenvM

val lookup_op : Name.operation -> (Mlty.ty list * Mlty.ty) tyenvM

val lookup_constructor : Name.constructor -> (Mlty.ty list * Mlty.ty) tyenvM

val lookup_continuation : (Mlty.ty * Mlty.ty) tyenvM

val add_var : Name.ident -> Mlty.ty -> 'a tyenvM -> 'a tyenvM

val add_equation : loc:Location.t -> Mlty.ty -> Mlty.ty -> unit tyenvM

val add_application : loc:Location.t -> Mlty.ty -> Mlty.ty -> Mlty.ty -> unit tyenvM

val add_lets : (Name.ident * Context.generalizable * Mlty.ty) list -> 'a tyenvM -> 'a tyenvM

val as_handler : loc:Location.t -> Mlty.ty -> (Mlty.ty * Mlty.ty) tyenvM

val as_ref : loc:Location.t -> Mlty.ty -> Mlty.ty tyenvM

val op_cases : Name.operation -> output:Mlty.ty -> (Mlty.ty list -> 'a tyenvM) -> 'a tyenvM

val at_toplevel : t -> 'a tyenvM -> 'a * t

val predefined_type : Name.ty -> Mlty.ty list -> Mlty.ty tyenvM

(** Toplevel functionality *)

val topadd_tydef : Name.ty -> Mlty.ty_def -> t -> t

val topadd_operation : Name.operation -> Mlty.ty list * Mlty.ty -> t -> t

val topadd_lets : (Name.ty * Context.generalizable * Mlty.ty) list -> t -> t

val apply_subst : t -> Mlty.ty -> Mlty.ty

