
(** Match a value against a pattern. Matches are returned in order of decreasing de bruijn index. *)
val match_pattern : Syntax.pattern -> Value.value -> Value.value list option Value.result

val multimatch_pattern : Syntax.pattern list -> Value.value list -> Value.value list option Value.result

