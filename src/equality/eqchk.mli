(** The type of equality checkers *)
type checker

(** The initial equality checker which can only handle α-equality *)
val empty_checker : checker

(** Add a type computation rule (also known as β-rule. XXX what about exceptions? *)
val add_type_computation : checker -> Nucleus.derivation -> checker

(** Add a term computation rule (also known as β-rule *)
val add_term_computation : checker -> Nucleus.derivation -> checker

(** Add an extensionality rule *)
val add_extensionality : checker -> Nucleus.derivation -> checker

(** Set the heads of a type symbol *)
val set_type_heads : checker -> Ident.t -> int list -> checker

(** Set the heads of a term symbol *)
val set_term_heads : checker -> Ident.t -> int list -> checker

(** The user-friendly interface, which figures out which kind of rule we are
   adding, and it guesses the heads. *)
val add : quiet:bool -> penv:Nucleus.print_environment -> checker -> Nucleus.derivation -> checker

(** Prove an abstracted type equality *)
val prove_eq_type_abstraction :
  checker -> Nucleus.signature -> Nucleus.eq_type_boundary Nucleus.abstraction -> Nucleus.eq_type_abstraction

(** Prove an abstracted term equality *)
val prove_eq_term_abstraction :
  checker -> Nucleus.signature -> Nucleus.eq_term_boundary Nucleus.abstraction -> Nucleus.eq_term_abstraction

(** Normalize a type *)
val normalize_type :
  strong:bool -> checker -> Nucleus.signature -> Nucleus.is_type -> Nucleus.eq_type * Nucleus.is_type

(** Normalize a term *)
val normalize_term :
  strong:bool -> checker -> Nucleus.signature -> Nucleus.is_term -> Nucleus.eq_term * Nucleus.is_term
