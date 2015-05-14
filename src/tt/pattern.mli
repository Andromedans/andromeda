(** Pattern matching support for hints. *)
type t
val of_term : Name.t list -> Tt.term' -> Tt.ty -> t
val pmatch : t -> Tt.term -> Tt.ty -> (Name.t * Tt.term) list option
