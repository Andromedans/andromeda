(** Evaluation of computations *)

(** [comp_value c] evaluates computation [c] in environment [env] and returns
    its value, or triggers a runtime error if the result is an operation. *)
val comp_value : Syntax.comp -> Value.value Value.toplevel

(** [comp_ty c] evaluates computation [c] in environment [env],
    checks that the result is a type and returns it. *)
val comp_ty : Syntax.comp -> Judgement.ty Value.toplevel

(** [comp_handle (xs,c)] makes the closure [fun xs => c]. *)
val comp_handle : (Name.ident list * Syntax.comp) -> (Value.value list,Value.value) Value.closure Value.toplevel

(** [comp_constant ryus c] evaluates the types for a constant declaration. *)
val comp_constant : (Name.ident * Syntax.comp) list -> Syntax.comp -> Tt.constsig Value.toplevel
