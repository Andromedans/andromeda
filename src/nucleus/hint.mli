val mk_beta : loc:Location.t -> Env.t ->
  (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction ->
  Pattern.hint_key * Pattern.beta_hint

val mk_eta : loc:Location.t -> Env.t ->
  (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction ->
  Pattern.hint_key * Pattern.eta_hint

val mk_general : loc:Location.t -> Env.t ->
  (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction ->
  Pattern.general_key * Pattern.general_hint

val mk_inhabit : loc:Location.t -> Env.t -> (Tt.ty, Tt.ty) Tt.abstraction ->
  Pattern.hint_key * Pattern.inhabit_hint
