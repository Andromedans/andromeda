(** Evaluation of computations *)

(** [comp env c] evaluates computation [c] in environment [env]. *)
val comp : Env.t -> Syntax.comp -> Value.result

(** [comp_value env] evaluates computation [c] in environment [env] and returns
    its value, or triggers a runtime error if the result is an operation. *)
val comp_value : Env.t -> Syntax.comp -> Value.value

(** [ty env c] evaluates computation [c] in environment [env],
    checks that the result is a type and returns it. *)
val ty : Env.t -> Syntax.comp -> Tt.ty
