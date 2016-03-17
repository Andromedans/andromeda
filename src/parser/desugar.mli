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

(** [toplevel basedir ctx c] desugars a toplevel command [c] with
    [ctx] information about bound names and [basedir] the directory used for relative inclusion paths. *)
val toplevel : basedir:string -> Ctx.t -> Input.toplevel -> Ctx.t * Syntax.toplevel

(** [file ctx fn] loads [fn] a path relative to the working directory or absolute.
    If [fn] has already been included it does nothing, returning the input context and the empty list. *)
val file : Ctx.t -> string -> Ctx.t * Syntax.toplevel list

