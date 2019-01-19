(** Predefined types and operations. *)

(** The Ocaml equivalent of the ML coercible type *)
type coercible =
  | NotCoercible
  | Convertible of Nucleus.eq_type_abstraction
  | Coercible of Nucleus.is_term_abstraction

(** Built-in Definitions *)

(** The list of built-in type, operation, and dynamic variable definitions
    corresponding to the names in Name.Predeclared, e.g.,
       - ['a list] and its constructors [[]] and [::]
       - ['a option] and its constructors [Some] and [None]
       - [coercible] and its constructors (as above)
       - operations [equal], [coerce]
       - the dynamic variable [hypotheses]
 *)
val definitions : Input.toplevel list

(** Runtime computations to invoke operations *)

(** A computation that, when run, invokes the [eq_term] operation on the given
    terms (wrapped as ML values), and then returns the resulting term equation if any.
 *)
val operation_equal_term :
  loc:Location.t -> Nucleus.is_term -> Nucleus.is_term -> Nucleus.eq_term option Runtime.comp

(** A computation that, when run, invokes the [eq_type] operation on the given
    terms (wrapped as ML values), and then returns the resulting term equation if any.
 *)
val operation_equal_type :
  loc:Location.t -> Nucleus.is_type -> Nucleus.is_type -> Nucleus.eq_type option Runtime.comp

(** A computation that, when run, invokes the [coerce] operation
    on the given type theory term and desired type, and decodes
    the resulting ML value as a value of the correponding ML type [coercible].
 *)
val operation_coerce :
  loc:Location.t -> Nucleus.is_term_abstraction -> Nucleus.is_type_abstraction -> coercible Runtime.comp

(** {6 translation between ML and ML values} *)

(** Decodes an ML list value as an ML list of ML values.
    Fails if the given value is not an ML [list].
 *)
val as_list : loc:Location.t -> Runtime.value -> Runtime.value list

(** Encodes a list of ML values as an ML list value
 *)
val mk_list : Runtime.value list -> Runtime.value

(** Encodes an ML option as an ML option
 *)
val from_option : Runtime.value option -> Runtime.value

(** Decodes an ML option as an ML option.
    Fails if the given value is not an ML [option]
 *)
val as_option : loc:Location.t -> Runtime.value -> Runtime.value option
