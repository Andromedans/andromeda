(* (\** Weak-head-normalization (multi-step) of a term *\) *)
(* val whnfs    : Context.t -> Syntax.term -> Syntax.ty -> Syntax.term *)

(* (\** Weak-head-normalization (multi-step) of a type *\) *)
(* val whnfs_ty : Context.t -> Syntax.ty -> Syntax.ty *)

(** Algorithmic type equality *)
val ty : Context.t -> Syntax.ty -> Syntax.ty -> bool

(** Express a type as a product *)
val as_prod : Context.t -> Syntax.ty -> (Syntax.name * Syntax.ty * Syntax.ty) option

(** Express a type as a path type *)
val as_paths : Context.t -> Syntax.ty -> (Syntax.ty * Syntax.term * Syntax.term) option

(** Express a type as a universe *)
val as_universe : Context.t -> Syntax.ty -> Universe.t option

(* (\** Algorithmic term equality at a type *\) *)
(* val term : Context.t -> Syntax.term -> Syntax.term -> Syntax.ty -> bool *)
