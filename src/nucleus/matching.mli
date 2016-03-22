
(** Match a value against a pattern. Matches are returned in order of decreasing de bruijn index. *)
val match_pattern : Syntax.pattern -> Runtime.value -> Runtime.value list option Runtime.comp

val match_op_pattern : Syntax.pattern list -> Syntax.pattern option ->
                       Runtime.value list ->    Jdg.ty option ->
                       Runtime.value list option Runtime.comp

