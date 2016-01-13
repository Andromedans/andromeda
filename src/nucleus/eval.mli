(** Evaluation of computations *)

(** [comp_value env] evaluates computation [c] in environment [env] and returns
    its value, or triggers a runtime error if the result is an operation. *)
val comp_value : Value.Env.t -> Syntax.comp -> Value.value

(** [comp_ty env c] evaluates computation [c] in environment [env],
    checks that the result is a type and returns it. *)
val comp_ty : Value.Env.t -> Syntax.comp -> Judgement.ty

(** [comp_handle env (xs,c)] makes the closure [fun xs => c]. *)
val comp_handle : Value.Env.t -> (Name.ident list * Syntax.comp) -> (Value.value list,Value.value) Value.closure

