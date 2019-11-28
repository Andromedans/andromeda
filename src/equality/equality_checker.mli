(** An equality checker *)
type checker

(** Indicate that a rule is not of the expected form *)
exception Invalid_rule

(** Indicate failure to verify an equality *)
exception Equality_fail

(** The default equality checker, it can only check for α-equality. *)
val empty_checker : checker

(** Add a β-rule to an equality checker, raise [Invalid_rule] if the
    form of the rule is not appropriate. *)
val add_beta : checker -> Nucleus.derivation -> checker

(** Add an extensionality rule to an equality checker, raise [Invalid_rule] if the
    form of the judgement is not appropriate. *)
val add_extensionality : checker -> Nucleus.derivation -> checker

(** Check a type equality, or raise [Equality_fail]. *)
val check_type_abstraction :
  checker -> Nucleus.signature -> Nucleus.is_type_abstraction -> Nucleus.is_type_abstraction ->
  Nucleus.eq_type_abstraction

(** Check a term equality, or raise [Equality_fail]. *)
val check_term_abstraction :
  checker -> Nucleus.signature -> Nucleus.is_term_abstraction -> Nucleus.is_term_abstraction ->
  Nucleus.eq_term_abstraction

(** Compute the weak head-normal form of a type. *)
val whnf_type : checker -> Nucleus.signature -> Nucleus.is_type -> Nucleus.eq_type

(** Compute the weak head-normal form of a term. *)
val whnf_term : checker -> Nucleus.signature -> Nucleus.is_term -> Nucleus.eq_term
