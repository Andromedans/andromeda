(** An equality checker *)
type checker

(** Indicate that a rule is not of the expected form *)
exception Invalid_rule

(** Indicate failure to verify an equality *)
exception Equality_fail

(** The default equality checker, it can only check for α-equality. *)
val empty_checker : checker

(** Add a type β-rule to an equality checker, raise [Invalid_rule] if the
    form of the rule is not appropriate. *)
val add_type_beta : checker -> Nucleus.derivation -> checker

(** Add a term β-rule to an equality checker, raise [Invalid_rule] if the
    form of the rule is not appropriate. *)
val add_term_beta : checker -> Nucleus.derivation -> checker

(** Add an extensionality rule to an equality checker, raise [Invalid_rule] if the
    form of the judgement is not appropriate. *)
val add_extensionality : checker -> Nucleus.derivation -> checker

(** Find a derivation of an abstracted type equality, or raise [Equality_fail]. *)
val prove_eq_type_abstraction :
  checker -> Nucleus.signature -> Nucleus.eq_type_boundary Nucleus.abstraction -> Nucleus.eq_type_abstraction

(** Find a derivation of an abstractd term equality, or raise [Equality_fail]. *)
val prove_eq_term_abstraction :
  checker -> Nucleus.signature -> Nucleus.eq_term_boundary Nucleus.abstraction -> Nucleus.eq_term_abstraction

(** Compute the weak head-normal form of a type. *)
val whnf_type : checker -> Nucleus.signature -> Nucleus.is_type -> Nucleus.eq_type

(** Compute the weak head-normal form of a term. *)
val whnf_term : checker -> Nucleus.signature -> Nucleus.is_term -> Nucleus.eq_term
