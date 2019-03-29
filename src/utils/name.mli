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
type path =
  | PName of t
  | PModule of path * t

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

(** Map a function on the values of a map *)
val map_fold : (t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b

(** [index x xs] finds the index of name [x] in list [xs] if it's there *)
val index : t -> t list -> int option

(** [index_opt x xs] finds the index of [x] in list of optional names [xs] if it's there. *)
val index_opt : t -> t option list -> int option

(** [level x xs] finds the level of [x] in list [xs] if it's there. *)
val level : t -> t list -> int option

(** Print a de Bruijn index, using its name from the list of given names *)
val print_debruijn : t list -> int -> Format.formatter -> unit

(** Predefined names assumed by ML to exist *)
module Builtin : sig
  (** The name of the ML module *)
  val ml_name : t
  val ml : path

  (** The name path to the boolean type *)
  val bool_name : t
  val bool : path

  (** The name of the [mlfalse] constructor *)
  val mlfalse_name : t
  val mlfalse : path

  (** The name of the [mltrue] constructor *)
  val mltrue_name : t
  val mltrue : path

  (** The name of the list type *)
  val list_name : t
  val list : path

  (** The name [[]] constructor *)
  val nil_name : t
  val nil : path

  (** The name of the [::] constructor *)
  val cons_name : t
  val cons : path

  (** The name of the order type *)
  val mlorder_name : t
  val mlorder : path

  (** The names of order type tags *)
  val mlless_name : t
  val mlless : path

  val mlequal_name : t
  val mlequal : path

  val mlgreater_name : t
  val mlgreater : path

  (** The name of the option type *)
  val option_name : t
  val option : path

  (** The name of the [Some] constructor *)
  val some_name : t
  val some : path

  (** The name of the [None] constructor *)
  val none_name : t
  val none : path

  (** The name of the [equal_term] operation *)
  val equal_term_name : t
  val equal_term : path

  (** The name of the [equal_type] operation *)
  val equal_type_name : t
  val equal_type : path

  (** The name of the [coercible] type *)
  val coercible_ty_name : t
  val coercible_ty : path

  (** The name of the [Coercible] constructor *)
  val coercible_constructor_name : t
  val coercible_constructor : path

  (** The name of the [Convertible] constructor *)
  val convertible_name : t
  val convertible : path

  (** The name of the [NotCoercible] constructor *)
  val notcoercible_name : t
  val notcoercible : path

  (** The name of the [coerce] operation *)
  val coerce_name : t
  val coerce : path

  (** The name of the [hypotheses] dynamic variable *)
  val hypotheses_name : t
  val hypotheses : path
end

module Json :
sig
  (** Convert an identifier to JSON. *)
  val name : t -> Json.t
end
