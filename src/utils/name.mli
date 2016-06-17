(** Variable names *)

(** The fixity classes charcterize the various kinds of identifiers. *)
type fixity =
  | Word (** an ordinary word *)
  | Anonymous of int (** an anonymous binder, written as [_] by the user *)
  | Prefix (** a prefix operator *)
  | Infix of Level.infix (** an infix operator of given level *)

type ident = private Ident of string * fixity

type atom = private Atom of string * fixity * int

(** Aliases with different semantics *)
type constant = ident
type operation = ident

type ty = ident
type constructor = ident

module Predefined : sig
  (** The name of the list type *)
  val list : ty

  (** The name [[]] constructor *)
  val nil : constructor

  (** The name of the [::] constructor *)
  val cons : constructor

  (** The name of the option type *)
  val option : ty

  (** The name of the [Some] constructor *)
  val some : constructor

  (** The name of the [None] constructor *)
  val none : constructor

  (** The name of the [equal] operation *)
  val equal : operation

  (** The name of the [as_prod] operation *)
  val as_prod : operation

  (** The name of the [as_eq] operation *)
  val as_eq : operation

  (** The name of the [coercible] type *)
  val coercible_ty : ty

  (** The name of the [Coercible] constructor *)
  val coercible_constructor : constructor

  (** The name of the [Convertible] constructor *)
  val convertible : constructor

  (** The name of the [NotCoercible] constructor *)
  val notcoercible : constructor

  (** The name of the [coerce] operation *)
  val coerce : operation

  (** The name of the [coerce_fun] operation *)
  val coerce_fun : operation

  (** The name of the [hypotheses] dynamic variable *)
  val hypotheses : ident
end

(** Convert an index to a greek letter, possibly with subscript. This is used
    for printing ML type parameters. *)
val greek : int -> string

(** Print a name. *)
val print_ident : ?parentheses:bool -> ident -> Format.formatter -> unit

(** Print an atom *)
type atom_printer
val atom_printer : unit -> atom_printer

(** Effectful: atoms are reindexed as they are encountered. *)
val print_atom : ?parentheses:bool -> printer:atom_printer -> atom -> Format.formatter -> unit

(** Print an operation name. *)
val print_op : ident -> Format.formatter -> unit

(** An new anonymous name that cannot be referenced by the user. *)
val anonymous : unit -> ident

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

(** Compare atoms. *)
val compare_atom : atom -> atom -> int

module AtomSet : Set.S with type elt = atom
module AtomMap : Map.S with type key = atom

(** [index_of_atom x xs] finds the index of [x] in list [xs] if it's there. *)
val index_of_atom : atom -> atom list -> int option

(** [index_of_ident x xs] finds the index of [x] in list [xs] if it's there. *)
val index_of_ident : ident -> ident list -> int option

(** [index_of_ident x xs] finds the level of [x] in list [xs] if it's there. *)
val level_of_ident : ident -> ident list -> int option

(** Like List.assoc, but using [eq_ident] and without exceptions. *)
val assoc_ident : ident -> (ident * 'a) list -> 'a option

val print_debruijn : ident list -> int -> Format.formatter -> unit

module Json :
sig
  (** Convert an identifier to JSON. *)
  val ident : ident -> Json.t

  (** Convert an atom to JSON. *)
  val atom : atom -> Json.t

  (** Convert a set of atoms to JSON. *)
  val atomset : AtomSet.t -> Json.t
end
