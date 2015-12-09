val mk_beta : loc:Location.t -> Environment.t ->
  Context.t -> Name.AtomSet.t -> (Tt.ty * Tt.term * Tt.term) Tt.ty_abstraction ->
  Pattern.hint_key * Pattern.beta_hint

val mk_eta : loc:Location.t -> Environment.t ->
  Context.t -> Name.AtomSet.t -> (Tt.ty * Tt.term * Tt.term) Tt.ty_abstraction ->
  Pattern.hint_key * Pattern.eta_hint

val mk_general : loc:Location.t -> Environment.t ->
  Context.t -> Name.AtomSet.t -> (Tt.ty * Tt.term * Tt.term) Tt.ty_abstraction ->
  Pattern.general_key * Pattern.general_hint

val mk_inhabit : loc:Location.t -> Environment.t ->
  Context.t -> Name.AtomSet.t -> Tt.ty Tt.ty_abstraction ->
  Pattern.hint_key * Pattern.inhabit_hint
