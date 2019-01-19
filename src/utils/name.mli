(** Names of defined entities (values, ML types, rules, etc.) *)

(** The fixity classes charcterize the various kinds of names. *)
type fixity =
  | Word (** an ordinary word *)
  | Anonymous of int (** an anonymous binder, written as [_] by the user *)
  | Prefix (** a prefix operator *)
  | Infix of Level.infix (** an infix operator of given level *)

(** Name *)
type t = private { name : string ; fixity : fixity }

(** A path to an entity *)
type path = private
  | PName of t
  | PModule of t * t

(** Make a nice subscript from an integer. *)
val subscript : int -> string

(** Convert an index to a greek letter, possibly with subscript. This is used
    for printing ML type parameters. *)
val greek : int -> string

(** Print a name *)
val print : ?parentheses:bool -> t -> Format.formatter -> unit

(** Print a path *)
val print_path : path -> Format.formatter -> unit

(** A new anonymous name that cannot be referenced by the user. *)
val anonymous : unit -> t

(** The basename of a file name associated with the given module name. *)
val module_filename : t -> string

(** Make a name from a string. *)
val mk_name : ?fixity:fixity -> string -> t

(** A path to a name without a module specification *)
val path_direct : t -> path

(** A path to a name in a module *)
val path_module : t -> t -> path

(** [refresh xs x] finds a nice variant of [x] that does not occur in [xs]. *)
val refresh : t list -> t -> t

(** Compare names for equality. *)
val equal : t -> t -> bool

(** A finite set of names *)
type set

(** The empty set of names *)
val set_empty : set

(** Add a name to a set *)
val set_add : t -> set -> set

(** Is the given name an element of the set? *)
val set_mem : t -> set -> bool

(** A map from names to values *)
type 'a map

(** The empty map *)
val map_empty : 'a map

(** Add a key-value pair to a map *)
val map_add : t -> 'a -> 'a map -> 'a map

(** Map a key to its value, or raise [Not_found] *)
val map_find : t -> 'a map -> 'a

(** Map a function on the values of a map *)
val map_map : ('a -> 'b) -> 'a map -> 'b map

(** [index x xs] finds the index of name [x] in list [xs] if it's there *)
val index : t -> t list -> int option

(** [index_opt x xs] finds the index of [x] in list of optional names [xs] if it's there. *)
val index_opt : t -> t option list -> int option

(** [level x xs] finds the level of [x] in list [xs] if it's there. *)
val level : t -> t list -> int option

(** Print a de Bruijn index, using its name from the list of given names *)
val print_debruijn : t list -> int -> Format.formatter -> unit

(** Predefined names assumed by ML to exist *)
module Predefined : sig
  (** The name of the boolean type *)
  val bool : t

  (** The name of the [mlfalse] constructor *)
  val mlfalse : t

  (** The name of the [mltrue] constructor *)
  val mltrue : t

  (** The name of the list type *)
  val list : t

  (** The name [[]] constructor *)
  val nil : t

  (** The name of the [::] constructor *)
  val cons : t

  (** The name of the order type *)
  val mlorder : t

  (** The names of order type tags *)
  val mlless : t
  val mlequal : t
  val mlgreater : t

  (** The name of the option type *)
  val option : t

  (** The name of the [Some] constructor *)
  val some : t

  (** The name of the [None] constructor *)
  val none : t

  (** The name of the [equal_term] operation *)
  val equal_term : t

  (** The name of the [equal_type] operation *)
  val equal_type : t

  (** The name of the [coercible] type *)
  val coercible_ty : t

  (** The name of the [Coercible] constructor *)
  val coercible_constructor : t

  (** The name of the [Convertible] constructor *)
  val convertible : t

  (** The name of the [NotCoercible] constructor *)
  val notcoercible : t

  (** The name of the [coerce] operation *)
  val coerce : t

  (** The name of the [hypotheses] dynamic variable *)
  val hypotheses : t
end

module Json :
sig
  (** Convert an identifier to JSON. *)
  val name : t -> Json.t
end
