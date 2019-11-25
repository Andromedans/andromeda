(** An equality checker *)
type checker

exception Invalid_rule

(** The default equality checker, it can only check for α-equality. *)
val empty_checker : checker

(** Add a β-rule to an equality checker, raise [Invalid_rule] if the
    form of the rule is not appropriate. *)
val add_beta : checker -> Nucleus.derivation -> checker

(** Add an extensionality rule to an equality checker, raise [Invalid_rule] if the
    form of the judgement is not appropriate. *)
val add_extensionality : checker -> Nucleus.derivation -> checker

(** Check a type equality. *)
val check_eqtype :
  checker -> Nucleus.is_type_abstraction -> Nucleus.is_type_abstraction ->
  Nucleus.eq_type_abstraction option

(** Check a term equality. *)
val check_eqterm :
  checker -> Nucleus.is_term_abstraction -> Nucleus.is_term_abstraction ->
  Nucleus.eq_term_abstraction option

(** Compute the weak head-normal form of a type. *)
val whnf_type : checker -> Nucleus.is_type_abstraction -> Nucleus.eq_type_abstraction

(** Compute the weak head-normal form of a term. *)
val whnf_term : checker -> Nucleus.is_term_abstraction -> Nucleus.eq_term_abstraction
