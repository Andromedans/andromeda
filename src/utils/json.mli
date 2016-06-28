(** The type representing JSON values (simplified) *)

(** We enforce the following conventions on exporting datatypes to JSON:

    - types which already exist in JSON are exported as such (ints, strings, lists, ...)

    - a value [{lbl1=v1; ... lblN=vN}] of record type [t] is exported as a dictionary
      [{"lbl1" : v1, .."lblN" : vN}]

    - a value [Tag (v1, ..., vN)] of sum type [t] is exported as [ ["Tag", v1, ..., vN] ]

    - a located value [{thing=v; loc=l}] is exported as [v], unless the [--json-location]
      option is used, in which case we use [ [v, loc] ].

    The exported JSON format does not hold typing information, but as long as
    we know what type to expect, the OCaml value can be reconstructed.
 *)

type t =
  | String of string
  | Int of int
  | List of t list
  | Dict of (t * t) list

(** [tuple lst] gives the JSON representation of a tuple with the given components. *)
val tuple : t list -> t

(** [record lst] gives the JSON representation of a record of type [ty] with fields and
    values described by the associative list [lst]. *)
val record : (string * t) list -> t

(** [tag "Tag" v] gives the JSON representation of a value of sum type [ty] with the
   given ["Tag"] and [data]. *)
val tag : string -> t list -> t

(** Nicely print an JSON expression *)
val print : t -> Format.formatter -> unit
