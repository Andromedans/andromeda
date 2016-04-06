
module TopEnv : sig
  type t
  
  val empty : t

  val add_tydef : Name.ty -> Amltype.ty_def -> t -> t

  val add_operation : Name.operation -> Amltype.ty list * Amltype.ty -> t -> t

  val gather_known : t -> Amltype.MetaSet.t

  val add_lets : (Name.ty * Context.generalizable * Amltype.ty) list -> t -> t
end

module Env : sig
  type 'a mon

  val return : 'a -> 'a mon

  val (>>=) : 'a mon -> ('a -> 'b mon) -> 'b mon

  val at_toplevel : TopEnv.t -> 'a mon -> 'a * TopEnv.t

  val lookup_var : Syntax.bound -> Amltype.ty mon

  val lookup_op : Name.operation -> (Amltype.ty list * Amltype.ty) mon

  val lookup_constructor : Name.constructor -> (Amltype.ty list * Amltype.ty) mon

  val lookup_continuation : (Amltype.ty * Amltype.ty) mon

  val add_var : Name.ident -> Amltype.ty -> 'a mon -> 'a mon

  val add_equation : loc:Location.t -> Amltype.ty -> Amltype.ty -> unit mon

  val add_application : loc:Location.t -> Amltype.ty -> Amltype.ty -> Amltype.ty -> unit mon

  val add_lets : (Name.ident * Context.generalizable * Amltype.ty) list -> 'a mon -> 'a mon

  val as_handler : loc:Location.t -> Amltype.ty -> (Amltype.ty * Amltype.ty) mon

  val as_ref : loc:Location.t -> Amltype.ty -> Amltype.ty mon

  val op_cases : Name.operation -> output:Amltype.ty -> (Amltype.ty list -> 'a mon) -> 'a mon

  val predefined_type : Name.ty -> Amltype.ty list -> Amltype.ty mon
end

