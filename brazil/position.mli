
(** The type of file positions *)
type t

(** Unknown position *)
val nowhere : t

(** Convert position to a string. *)
val to_string : ?full:bool -> t -> string

