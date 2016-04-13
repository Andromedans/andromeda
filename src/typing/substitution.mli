(** Type metavariable substitutions. *)

(** The type of substitutions. *)
type t

(** The empty substitution. *)
val empty : t

(** The domain of a substitution. *)
val domain : t -> Mlty.MetaSet.t

(** [lookup m s] gives the current binding of [m] in [s]. That binding may contain metavariables bound in [s]. *)
val lookup : Mlty.meta -> t -> Mlty.ty option

(** [apply s t] applies [s] to the metavariables in [t] recursively.
    [apply s] is idempotent: [apply s (apply s t)] is equal to [apply s t]. *)
val apply : t -> Mlty.ty -> Mlty.ty

(** [from_lists ms ts] creates the substitution which to [m] at index [i] in [ms] associates [t] at index [i] in [ts]. *)
val from_lists : Mlty.meta list -> Mlty.ty list -> t

(** Add a binding to a substitution. If doing so would create a loop, raises an error. *)
val add : Mlty.meta -> Mlty.ty -> t -> t option

(** [partition p s] returns [s1, s2] where [s1] is the bindings verifying [p] and [s2] are the others. *)
val partition : (Mlty.meta -> Mlty.ty -> bool) -> t -> t * t

