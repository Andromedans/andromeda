
(** Match a value against a pattern. Matches are returned in order of decreasing de bruijn index. *)
val match_pattern : Pattern.pattern -> Runtime.value -> Runtime.value list option Runtime.comp

val match_op_pattern :
  Pattern.pattern list -> Pattern.pattern option ->
  Runtime.value list -> Jdg.ty option ->
  Runtime.value list option Runtime.comp
