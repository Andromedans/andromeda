(** The type of beta hints *)
type beta

(** The type of eta hints *)
type eta

(** Compile an expression to a beta hint *)
val mk_beta : Tt.ty -> beta

(** Compile an expression to an eta hint *)
val mk_eta : Tt.ty -> eta
