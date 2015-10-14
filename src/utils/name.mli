(** Variable names *)

(** Type of names, exposed for debugging purposes. *)
type ident = private
  | Anonymous
  | String of string

(** Type of a name à la nominal calculus used to evaluate under binders *)
type atom = private
  | Gensym of string * int

(** Print a name. *)
val print_ident : ident -> Format.formatter -> unit

(** Print an atom *)
val print_atom : atom -> Format.formatter -> unit

(** Print an operation name. *)
val print_op : string -> Format.formatter -> unit

(** An anonymous name that cannot be referenced. *)
val anonymous : ident

(** Make a name from a string. *)
val make : string -> ident

(** Generate a variant of a given name that is guaranteed to not yet exist. *)
val fresh : ident -> atom

(** Generate a fresh name to be used in desugaring. *)
val fresh_candy : unit -> ident

(** [refresh xs x] finds a nice variant of [x] that does not occur in [xs]. *)
val refresh : ident list -> ident -> ident

(** Compare identifiers. *)
val eq_ident : ident -> ident -> bool

(** Compare atoms for equality. *)
val eq_atom : atom -> atom -> bool

(** Compare atoms. *)
val compare_atom : atom -> atom -> int

(** [index_of_atom x xs] finds the index of [x] in list [xs] if it's there. *)
val index_of_atom : atom -> atom list -> int option

(** [index_of_ident x xs] finds the index of [x] in list [xs] if it's there. *)
val index_of_ident : ident -> ident list -> int option

val print_binder1 :
  (ident list -> 'a -> Format.formatter -> unit) -> ident list ->
  ident -> 'a -> Format.formatter -> unit

val print_binders :
  (ident list -> ident -> 'a -> Format.formatter -> unit) ->
  (ident list -> Format.formatter -> unit) ->
  ident list -> (ident * 'a) list ->
  Format.formatter -> unit
