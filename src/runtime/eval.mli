(** [ceval ctx c] evaluates command [c] in context [ctx]. *)
val infer : Context.t -> Syntax.comp -> Value.result

(** [ty ctx c] evaluates command [c] in context [ctx] and
    checks that the result is a type. *)
val ty : Context.t -> Syntax.comp -> Value.ty
