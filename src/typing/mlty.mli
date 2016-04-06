(** Type checking of the metalanguage. *)

(** The errors reported by type inference. *)
type error

exception Error of error Location.located

val print_error : error -> Format.formatter -> unit

(** Typing environment. *)
module TopEnv : sig
  type t

  val empty : t
end

(** [toplevel env c] checks that toplevel command [c] is well typed and updates the environment accordingly. *)
val toplevel : TopEnv.t -> Syntax.toplevel -> TopEnv.t

