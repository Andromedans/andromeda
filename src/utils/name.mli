(** Variable names *)

(** Type of names, exposed for debugging purposes. *)
type t = private
  | Anonymous
  | Gensym of string * int
  | String of string

(** Print a name. *)
val print : t -> Format.formatter -> unit

(** An anonymous name that cannot be referenced. *)
val anonymous : t

(** Make a name from a string. *)
val make : string -> t

(** Generate a variant of a given name that is guaranteed to not yet exist. *)
val fresh : t -> t

(** [refresh xs x] finds a nice variant of [x] that does not occur in [xs]. *)
val refresh : t list -> t -> t

(** Compare names. *)
val eq : t -> t -> bool

(** [index_of x xs] finds the index of [x] in list [xs]. *)
val index_of : t -> t list -> int option
val print_binder1 :
  (t list -> 'a -> Format.formatter -> unit) -> t list ->
  t -> 'a -> Format.formatter -> unit
val print_binders :
  (t list -> t -> 'a -> Format.formatter -> unit) ->
  (t list -> Format.formatter -> unit) ->
  t list -> (t * 'a) list ->
  Format.formatter -> unit
