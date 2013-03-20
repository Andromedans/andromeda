open Context

type value =
  | EqWtn of Syntax.term * Syntax.term * Syntax.sort
  | TyWtn of Syntax.term * Syntax.sort
  | Lambda of Common.variable * Syntax.sort * value

type result =
  | Value of value
  | Operation of Syntax.operation * closure
  | Abstraction of Common.variable * Syntax.sort * result * closure

and closure = value -> result

let rec to_term ctx = function
  | EqWtn (e1, e2, t) ->
    Syntax.mk_eqwtn e1 e2 t, Syntax.mk_eqjdg e1 e2 t
  | TyWtn (e, t) ->
    Syntax.mk_tywtn e t, Syntax.mk_tyjdg e t
  | Lambda (x, t, v) ->
    let e, s = to_term (add_parameter x t ctx) v in
      Syntax.mk_lambda x (Some t) e, Syntax.mk_pi x t s

