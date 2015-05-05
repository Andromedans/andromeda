(** The type of beta hints *)
type beta_hint

(** The type of eta hints *)
type eta_hint

(** Compile an expression to a beta hint *)
val mk_beta : Tt.ty -> beta_hint

(** Compile an expression to an eta hint *)
val mk_eta : Tt.ty -> eta_hint

(** Match a beta hint against a term. On success return the rewritten term. *)
val match_beta : beta_hint -> Tt.term -> Tt.term option

(** Match an eta hint against an equality type (already decomposed as two terms and a type).
    On success return a list of types that need to be inhabited for the match to succeed.
    These types should be universally quantified equality types (for now).
*)
val match_eta : eta_hint -> Tt.term -> Tt.term -> Tt.ty -> (Tt.ty list) option