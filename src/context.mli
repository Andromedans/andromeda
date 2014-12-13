(** A context entry is either a free variable of a given type,
    or a value binding. *)
type entry = private
  | Entry_free of Syntax.ty        (* a free variable *)
  | Entry_value of Syntax.value    (* a variable bound by a [let] *)

(** The type of contexts *)
type t = (Common.name * entry) list

(** The empty context *)
val empty : t

(** Lookup a context entry *)
val lookup : Common.name -> t -> entry option

(** Is the given name bound as a free variable? *)
val is_free : Common.name -> t -> bool

(** Is the given name bound to a value? *)
val is_value : Common.name -> t -> bool

(** Is the given name bound? *)
val is_bound : Common.name -> t -> bool

(** Add a free variable with suggested name and a given type to the context.
    The result is the actual name bound (it may change to avoid shadowing)
    and the modified context. *)
val add_free : Common.name -> Syntax.ty -> t -> Common.name * t 

(** Bind a name to a value, raising an error if shadowing would occur. *)
val add_value : Common.name -> Syntax.value -> t -> t
