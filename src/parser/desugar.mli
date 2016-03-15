(** Conversion from sugared to desugared input syntax *)


(** Parser wrapper that reads extra lines on demand. *)
val parse : ('a -> 'b -> 'c) -> 'a -> 'b -> 'c

(** A module which holds the desugaring context *)
module Ctx : sig
  (** The type of desugaring context *)
  type t

  (** Empty desugaring context *)
  val empty : t
end

(** [toplevel primitive bound c] desugars a toplevel command [c] with a
    list of primitives and their arities, and a list of bound variables
    that are converted to de Bruijn indiced. *)
val toplevel : basedir:string -> Ctx.t -> Input.toplevel -> Ctx.t * Syntax.toplevel

(** [file limit ctx fn] loads [fn] a path relative to the working directory or absolute.
    If [fn] has already been included it does nothing, returning the input context and the empty list. *)
val file : Ctx.t -> string -> Ctx.t * Syntax.toplevel list

