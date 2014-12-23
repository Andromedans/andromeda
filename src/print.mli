val verbosity : int ref
val annotate : bool ref
module StringSet :
  sig
    type elt = string
    type t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val of_list : elt list -> t
  end
val displayable : StringSet.t ref
val message :
  string -> int -> ('a, Format.formatter, unit, unit) format4 -> 'a
val error : 'a * string * string -> unit
val warning : ('a, Format.formatter, unit, unit) format4 -> 'a
val debug :
  ?category:StringSet.elt -> ('a, Format.formatter, unit, unit) format4 -> 'a
val print :
  ?max_level:int ->
  ?at_level:int ->
  Format.formatter -> ('a, Format.formatter, unit, unit) format4 -> 'a
val annot :
  ?prefix:string -> (Format.formatter -> unit) -> Format.formatter -> unit
val sequence :
  ?sep:string ->
  ('a -> Format.formatter -> unit) -> 'a list -> Format.formatter -> unit
val name : Common.name -> Format.formatter -> unit
val prod :
  ?max_level:int ->
  Context.t ->
  Common.name -> Syntax.ty -> Syntax.bare_ty -> Format.formatter -> unit
val lambda :
  Context.t ->
  Common.name ->
  Syntax.ty -> Syntax.bare_ty -> Syntax.bare_term -> Format.formatter -> unit
val term :
  ?max_level:int -> Context.t -> Syntax.term -> Format.formatter -> unit
val ty : ?max_level:int -> Context.t -> Syntax.ty -> Format.formatter -> unit
val value :
  ?max_level:'a -> Context.t -> Syntax.value -> Format.formatter -> unit
val context : Context.t -> Format.formatter -> unit
