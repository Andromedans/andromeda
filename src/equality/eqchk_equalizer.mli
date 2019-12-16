(** The type of equality checkers *)
type checker

(** The initial equality checker which can only handle α-equality *)
val empty_checker : checker

(** Add a type computation rule (also known as β-rule. XXX what about exceptions? *)
val add_type_computation : checker -> Nucleus.derivation -> checker

(** Add a term computation rule (also known as β-rule *)
val add_term_computation : checker -> Nucleus.derivation -> checker
