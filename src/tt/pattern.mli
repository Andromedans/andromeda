(** Pattern matching support for hints. *)

(** Alas, "match" is a reserved word, so we use "combine". If you can think of
    a better one, please fix. *)
val combine : Tt.term -> Tt.term -> (Name.t * Tt.term) list option

val combine_ty : Tt.ty -> Tt.ty -> (Name.t * Tt.term) list option