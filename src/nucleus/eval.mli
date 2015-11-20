(** Evaluation of computations *)

(** [beta_bind env lst] evaluates the beta hints given in [lst] and returns
    the environment [env] extended with the hints. *)
val beta_bind : Environment.t -> (string list * Syntax.comp) list -> Environment.t Value.result

(** [eta_bind env lst] evaluates the eta hints given in [lst] and returns
    the environment [env] extended with the hints. *)
val eta_bind : Environment.t -> (string list * Syntax.comp) list -> Environment.t Value.result

(** [hint_bind env lst] evaluates the general hints given in [lst] and returns
    the environment [env] extended with the hints. *)
val hint_bind : Environment.t -> (string list * Syntax.comp) list -> Environment.t Value.result

(** [inhabit_bind env lst] evaluates the inhabit hints given in [lst] and returns
    the environment [env] extended with the hints. *)
val inhabit_bind : Environment.t -> (string list * Syntax.comp) list -> Environment.t Value.result

(** [comp_value env] evaluates computation [c] in environment [env] and returns
    its value, or triggers a runtime error if the result is an operation. *)
val comp_value : Environment.t -> Syntax.comp -> Value.value

(** [comp_ty env c] evaluates computation [c] in environment [env],
    checks that the result is a type and returns it. *)
val comp_ty : Environment.t -> Syntax.comp -> Judgement.ty
