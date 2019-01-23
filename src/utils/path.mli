(** Access paths to entites in mmodules *)

(** A de Bruijn index *)
type index = Index of Name.t * int

(** A de Bruijn level *)
type level = Level of Name.t * int

(** An access path is a reference to a named entity in a module. *)
type t =
  | Direct of level
  | Module of level * level

(** Access path to an ML constructor *)
type ml_constructor = t * level

(** print a path *)
val print : t -> Format.formatter -> unit
