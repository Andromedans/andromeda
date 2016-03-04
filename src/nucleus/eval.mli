(** Evaluation of computations *)

val infer : Syntax.comp -> Value.value Value.comp

val check_ty : Syntax.comp -> Jdg.ty Value.comp

