(** Evaluation of computations *)

(** [comp env c] evaluates computation [c] in environment [env]. *)
val comp : Environment.t -> Syntax.comp -> Value.result

(** [comp_value env] evaluates computation [c] in environment [env] and returns
    its value, or triggers a runtime error if the result is an operation. *)
val comp_value : Environment.t -> Syntax.comp -> Value.value

(** [comp_term env c] evaluates computation [c] in environment [env],
    checks that the result is a term and returns it. *)
val comp_term : Environment.t -> Syntax.comp -> Judgement.term

(** [comp_ty env c] evaluates computation [c] in environment [env],
    checks that the result is a type and returns it. *)
val comp_ty : Environment.t -> Syntax.comp -> Judgement.ty
