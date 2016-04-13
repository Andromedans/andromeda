(** The type representing JSON values (simplified) *)

(** We enforce the following conventions on exporting
    datatypes to JSON:

    - types which already exist in JSON are exported as such (ints, strings, lists, ...)
    - a value [{lbl1=v1; ... lblN=vN}] of record type [t] is exported as a dictionary

        [{ "_ty" : "t",
          "lbl1" : v1,
          ..
          "lblN" : vN }]

    - a value [Tag v] of sum type [t] is exported as

        [{ "_ty" : "t",
          "tag" : "Tag",
          "data" : v }]

    - if the tag does not have any [v] associated with it then the [data] key is omitted.

    - if the sum has single tag then the tag is ommited

    There is of course an opportunity here for some generic programming,
    OCaml ppx magic etc., but let's resist the urge to get fancy for at
    least a little while.
 *)

type t =
  | String of string
  | Int of int
  | List of t list
  | Dict of (t * t) list

(** [of_ty ty d] gives the JSON dictionary [d] with the additional entry ["_ty" : String ty]. *)
val of_ty : string -> (string * t) list -> t

(** [tuple lst] gives the JSON representation of a tuple with the given components. *)
val tuple : t list -> t

(** [record ty d] gives the JSON representation of a record of type [ty] with fields and
    values [d]. *)
val record : string -> (string * t) list -> t

(** [tag ty "Tag" v] gives the JSON representation of a value of sum type [ty] with the
   given ["Tag"] and [data]. *)
val tag : string -> string -> t list -> t
                        
(** Nicely print an s-expression *)
val print : t -> Format.formatter -> unit
