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

(** [file ctx fn] loads [fn] a path relative to the working directory or absolute.
    If [fn] has already been included it does nothing, returning the input context and the empty list. *)
val file : Ctx.t -> string -> Ctx.t * Dsyntax.toplevel list

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
  val mlfalse : Path.ml_constructor * arity
  val mltrue : Path.ml_constructor * arity

  val list : Path.t
  val nil : Path.ml_constructor * arity
  val cons : Path.ml_constructor * arity

  val option : Path.t
  val none : Path.ml_constructor * arity
  val some : Path.ml_constructor * arity

  val notcoercible : Path.ml_constructor * arity
  val convertible : Path.ml_constructor * arity
  val coercible_constructor : Path.ml_constructor * arity

  val equal_term : Path.t * arity
  val equal_type : Path.t * arity
  val coerce : Path.t * arity


  (** Get the de Bruijn index of the builting value [hypotheses].

  This is a bit inefficient as we look it up at runtime every time we access it. To fix
     the problem, all the builtin entities should be place in a module and then we can use
     levels, which do not change. *)
  val hypotheses : Ctx.t -> Path.index
end
