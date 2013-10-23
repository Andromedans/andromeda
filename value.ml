open Context

type value =
  | Lambda of Common.variable * Syntax.ty * value

type result =
  | Value of value
  | Operation of Syntax.operation * closure
  | Abstraction of Common.variable * Syntax.ty * result * closure
  | Definition of Common.variable * Syntax.ty * Syntax.expr * result * closure

and closure = value -> result
