(** Runtime values and results *)

(** A value is the result of a computation. *)
type value = Tt.term * Tt.ty

(** A result of computation *)
type result =
  | Return of value

val print : ?max_level:int -> Name.t list -> value -> Format.formatter -> unit
