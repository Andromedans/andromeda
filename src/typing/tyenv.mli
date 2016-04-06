
module TopEnv : sig
  type t

  val empty : t

  val add_tydef : Name.ty -> Mlty.ty_def -> t -> t

  val add_operation : Name.operation -> Mlty.ty list * Mlty.ty -> t -> t

  val gather_known : t -> Mlty.MetaSet.t

  val add_lets : (Name.ty * Context.generalizable * Mlty.ty) list -> t -> t
end

module Env : sig
  type 'a mon

  val return : 'a -> 'a mon

  val (>>=) : 'a mon -> ('a -> 'b mon) -> 'b mon

  val at_toplevel : TopEnv.t -> 'a mon -> 'a * TopEnv.t

  val lookup_var : Syntax.bound -> Mlty.ty mon

  val lookup_op : Name.operation -> (Mlty.ty list * Mlty.ty) mon

  val lookup_constructor : Name.constructor -> (Mlty.ty list * Mlty.ty) mon

  val lookup_continuation : (Mlty.ty * Mlty.ty) mon

  val add_var : Name.ident -> Mlty.ty -> 'a mon -> 'a mon

  val add_equation : loc:Location.t -> Mlty.ty -> Mlty.ty -> unit mon

  val add_application : loc:Location.t -> Mlty.ty -> Mlty.ty -> Mlty.ty -> unit mon

  val add_lets : (Name.ident * Context.generalizable * Mlty.ty) list -> 'a mon -> 'a mon

  val as_handler : loc:Location.t -> Mlty.ty -> (Mlty.ty * Mlty.ty) mon

  val as_ref : loc:Location.t -> Mlty.ty -> Mlty.ty mon

  val op_cases : Name.operation -> output:Mlty.ty -> (Mlty.ty list -> 'a mon) -> 'a mon

  val predefined_type : Name.ty -> Mlty.ty list -> Mlty.ty mon
end

