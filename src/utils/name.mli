(** Variable names *)

type fixity =
  | Word
  | Anonymous
  | Prefix
  | Infix0
  | Infix1
  | Infix2
  | Infix3
  | Infix4

type ident = private Ident of string * fixity

type atom = private Atom of string * fixity * int

(** The type of a structure or signature field. *)
type label = ident

(** The type of a signature name. *)
type signature = ident

(** Print a name. *)
val print_ident : ident -> Format.formatter -> unit

(** Print an atom *)
val print_atom : atom -> Format.formatter -> unit

(** Print a field label *)
val print_label : label -> Format.formatter -> unit

(** Print an operation name. *)
val print_op : ident -> Format.formatter -> unit

(** An anonymous name that cannot be referenced. *)
val anonymous : ident

(** Is the given identifier anonymous? *)
val is_anonymous : ident -> bool

(** Make a name from a string. *)
val make : ?fixity:fixity -> string -> ident

(** Generate a variant of a given name that is guaranteed to not yet exist. *)
val fresh : ident -> atom

(** [refresh xs x] finds a nice variant of [x] that does not occur in [xs]. *)
val refresh : ident list -> ident -> ident

(** Compare identifiers for equality. *)
val eq_ident : ident -> ident -> bool

(** Compare identifiers. *)
val compare_ident : ident -> ident -> int

module IdentMap : Map.S with type key = ident

(** Compare atoms for equality. *)
val eq_atom : atom -> atom -> bool

(** Compare labels for equality. *)
val eq_label : label -> label -> bool

(** Compare atoms. *)
val compare_atom : atom -> atom -> int

module AtomSet : Set.S with type elt = atom

(** [index_of_atom x xs] finds the index of [x] in list [xs] if it's there. *)
val index_of_atom : atom -> atom list -> int option

(** [index_of_ident x xs] finds the index of [x] in list [xs] if it's there. *)
val index_of_ident : ident -> ident list -> int option
