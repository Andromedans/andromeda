
module Ctx : sig

  type t

  val empty : t

end

val toplevel : Ctx.t -> Syntax.toplevel -> Ctx.t
