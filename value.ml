open Context

type value =
  | Lambda of Common.variable * Syntax.sort * value

type result =
  | Value of value
  | Operation of Syntax.operation * closure
  | Abstraction of Common.variable * Syntax.sort * result * closure
  | Definition of Common.variable * Syntax.sort * Syntax.term * result * closure

and closure = value -> result
