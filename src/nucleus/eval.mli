(** Evaluation of computations *)

val infer : Syntax.comp -> Runtime.value Runtime.comp

val check_ty : Syntax.comp -> Jdg.ty Runtime.comp

