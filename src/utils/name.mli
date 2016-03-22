(** Variable names *)

type fixity =
  | Word
  | Anonymous
  | Prefix
  | Infix of Level.infix

type ident = private Ident of string * fixity

type atom = private Atom of string * fixity * int

(** A name environment tells us how to print atoms found in it. *)
type env = (atom * ident) list

(** Aliases with different semantics *)
type label = ident
type signature = ident
type constant = ident
type operation = ident

type ty = ident
type constructor = ident

(** The name of empty list *)
val nil : ident

(** The name of the cons constructor *)
val cons : ident

(** Print a name. *)
val print_ident : ?parentheses:bool -> ident -> Format.formatter -> unit

(** Print an atom *)
val print_atom : ?parentheses:bool -> ?penv:env -> atom -> Format.formatter -> unit

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

val ident_of_atom : atom -> ident

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

(** Like List.assoc, but using [eq_ident] and without exceptions. *)
val assoc_ident : ident -> (ident * 'a) list -> 'a option

val print_debruijn : ident list -> int -> Format.formatter -> unit

