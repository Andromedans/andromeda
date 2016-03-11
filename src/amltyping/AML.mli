type ty

module Ctx : sig

  type t

  val empty : t

end

val infer : Syntax.toplevel -> Ctx.t -> Ctx.t
