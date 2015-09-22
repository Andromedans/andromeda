(** Evaluation of computations *)

(** [comp env c] evaluates computation [c] in environment [env]. *)
val comp : Environment.t -> Syntax.comp -> Value.result

(** [comp_value env] evaluates computation [c] in environment [env] and returns
    its value, or triggers a runtime error if the result is an operation. *)
val comp_value : Environment.t -> Syntax.comp -> Value.value

(** [ty env c] evaluates computation [c] in environment [env],
    checks that the result is a type and returns it. *)
val ty : Environment.t -> Syntax.comp -> Tt.ty
