
val mk_beta : loc:Location.t -> Context.t -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction -> Pattern.beta_hint

val mk_eta : loc:Location.t -> Context.t -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction -> Pattern.eta_hint

val mk_general : loc:Location.t -> Context.t -> (Tt.ty, Tt.ty * Tt.term * Tt.term) Tt.abstraction -> Pattern.general_hint

val mk_inhabit : loc:Location.t -> Context.t -> (Tt.ty, Tt.ty) Tt.abstraction -> Pattern.inhabit_hint
