(** Simplification of expressions and types. *)

val simplify : Context.t -> Tt.term -> Tt.term

val simplify_ty : Context.t -> Tt.ty -> Tt.ty
