
module Ctx : sig

  type t

  val empty : t

end

val infer : Ctx.t -> Syntax.toplevel -> Ctx.t
