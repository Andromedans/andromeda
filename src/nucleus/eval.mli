(** Evaluation of computations *)

(** [comp ctx c] evaluates computation [c] in context [ctx]. *)
val comp : Context.t -> Syntax.comp -> Value.result

(** [comp_value ctx] evaluates computation [c] in context [ctx] and returns
    its value, or triggers a runtime error if the result is an operation. *)
val comp_value : Context.t -> Syntax.comp -> Value.value

(** [ty ctx c] evaluates computation [c] in context [ctx] and
    checks that the result is a type. *)
val ty : Context.t -> Syntax.comp -> Tt.ty
