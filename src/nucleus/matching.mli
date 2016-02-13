
(** Match a value against a pattern. Matches are returned in order of decreasing de bruijn index. *)
val match_pattern : Syntax.pattern -> Value.value -> Value.value list option Value.result

val match_op_pattern : Syntax.pattern list -> Syntax.pattern option ->
                       Value.value list ->    Jdg.ty option ->
                       Value.value list option Value.result

