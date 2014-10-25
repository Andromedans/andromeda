(** Variable names
 *)
type name = string

(** De Bruijn indices
 *)
type debruijn = int

(** A side-effecting counter that returns a different number (as a string) each time it is
    called. Mainly used for marking output in debugging messages. *)
val next : unit -> string

