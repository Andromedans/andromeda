(** [ceval ctx c] evaluates command [c] in context [ctx]. *)
val ceval : Context.t -> Input.comp -> Syntax.value

(** [is_type ctx t] checks that [t] is a type in context [ctx]
    and returns its [Syntax] form. *)
val is_type : Context.t -> Input.ty -> Syntax.ty
