(** Conversion from sugared to desugared input syntax *)

type error

(** The arity of a constructor or an operation *)
type arity = int

val print_error : error -> Format.formatter -> unit

exception Error of error Location.located

(** A module which holds the desugaring context *)
module Ctx : sig
  (** The type of desugaring context *)
  type t

  (** Empty desugaring context *)
  val empty : t
end

(** [toplevel basedir ctx c] desugars a toplevel command [c] with
    [ctx] information about bound names and [basedir] the directory used for relative inclusion paths. *)
val toplevel : basedir:string -> Ctx.t -> Input.toplevel -> Ctx.t * Dsyntax.toplevel

(** [use_file ctx fn] loads the file with the given filename.  *)
val use_file : Ctx.t -> string -> Ctx.t * Dsyntax.toplevel list

(** The initial desugaring context, with built-in types and operations *)
val initial_context : Ctx.t

(** A list of toplevel commands that must be type-checked and evaluated
    in order to setup the typing and runtime environment that corresponds
    to [initial_context]. *)
val initial_commands : Dsyntax.toplevel list

(** Access paths and arities of builtin constructors and arities *)
module Builtin :
sig
  val bool : Path.t
  val mlfalse : Path.ml_constructor
  val mltrue : Path.ml_constructor

  val list : Path.t
  val nil : Path.ml_constructor
  val cons : Path.ml_constructor

  val option : Path.t
  val none : Path.ml_constructor
  val some : Path.ml_constructor

  val notcoercible : Path.ml_constructor
  val convertible : Path.ml_constructor
  val coercible_constructor : Path.ml_constructor

  val mlless : Path.ml_constructor
  val mlequal : Path.ml_constructor
  val mlgreater : Path.ml_constructor

  val equal_term : Path.t
  val equal_type : Path.t
  val coerce : Path.t
  val hypotheses : Path.t
end
