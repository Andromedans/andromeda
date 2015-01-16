(** [comp ctx c] evaluates computation [c] in context [ctx]. *)
val comp : Context.t -> Syntax.comp -> Value.result

(** [ty ctx c] evaluates computation [c] in context [ctx] and
    checks that the result is a type. *)
val ty : Context.t -> Syntax.comp -> Tt.ty
