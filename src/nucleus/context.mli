(** Typing context and runtime environment *)

(** A typing context with a runtime environment, we refer to it as just context *)
type t

(** The empty context *)
val empty : t

(** List of primitive names with their arities. *)
val primitives : t -> (Name.t * int) list

(** Known bound variables *)
val bound_names : t -> Name.t list

(** Variable names already used in the context *)
val used_names : t -> Name.t list

(** Lookup a primitive operation. *)
val lookup_primitive : Name.t -> t -> Tt.primsig option

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : Syntax.bound -> t -> Value.value

(** Return all beta hints in the context *)
val beta_hints : Pattern.hint_key -> t -> Pattern.beta_hint list

(** Return all eta hints in the context *)
val eta_hints : Pattern.hint_key -> t -> Pattern.eta_hint list

(** Return all general hints in the context *)
val general_hints : (Pattern.hint_key * Pattern.hint_key * Pattern.hint_key) option ->
  t -> Pattern.general_hint list

(** Return all general hints in the context *)
val inhabit_hints : Pattern.hint_key -> t -> Pattern.inhabit_hint list

(** Add a primitive operation of a given signature to the context.
    Fails if the variable is already bound. *)
val add_primitive : Name.t -> Tt.primsig -> t -> t

(** Add a beta hint to the context. *)
val add_betas : (string list * (Pattern.hint_key * Pattern.beta_hint)) list -> t -> t

(** Add an eta hint to the context. *)
val add_etas : (string list * (Pattern.hint_key * Pattern.eta_hint)) list -> t -> t

(** Add a general hint to the context. *)
val add_generals :
  (string list *
   ((Pattern.hint_key * Pattern.hint_key * Pattern.hint_key) option * Pattern.general_hint)) list ->
  t -> t

(** Add an inhabit hint to the context. *)
val add_inhabits : (string list * (Pattern.hint_key * Pattern.inhabit_hint)) list -> t -> t

(** Remove all hints with one of the given tags *)
val unhint : string list -> t -> t

(** Add a bound variable with given name to the context. *)
val add_bound : Name.t -> Value.value -> t -> t

(** Add a file to the list of files included. *)
val add_file : string -> t -> t

(** Check whether a file has already been included. Files are compared by
    their basenames *)
val included : string -> t -> bool

(** Print free variables in the context *)
val print : t -> Format.formatter -> unit
