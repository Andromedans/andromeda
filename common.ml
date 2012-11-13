(** Types and definitions in common use. *)

(** Position in source code. For each type in the abstract syntax we define two versions
    [t] and [t']. The former is the latter with a position tag. For example, [expr = expr'
    * position] and [expr'] is the type of expressions (without positions). 
*)
type position =
  | Position of Lexing.position * Lexing.position (** delimited position *)
  | Nowhere (** unknown position *)

(** During substitution we generate fresh variable names. Because we want pretty printing,
    each freshly generated variable name should "remember" its preferred form. Thus a
    variable name has three possible form. It can be a string, as originally given by
    the user, or it can be a generated fresh name consisting of preferred name and a counter,
    or it can be a dummy, indicating that it is never used.
*)
type variable =
  | String of string
  | Gensym of string * int
  | Anonymous

(** [refresh x] generates a fresh variable name whose preferred form is [x]. *)
let refresh =
  let k = ref 0 in
    function
      | String x | Gensym (x, _) -> (incr k ; Gensym (x, !k))
      | Anonymous -> (incr k ; Gensym ("_", !k))

(** [nowhere e] is the expression [e] without a source position. It is used when
    an expression is generated and there is not reasonable position that could be
    assigned to it. *)
let nowhere x = (x, Nowhere)

