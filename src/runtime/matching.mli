
(** Match a value against a pattern. Matches are returned in order of decreasing de Bruijn index. *)
val match_pattern : Pattern.aml -> Runtime.value -> Runtime.value list option Runtime.comp

(** Match a value against a pattern. Matches are returned in the order of decreasing de Bruijn index. *)
val top_match_pattern : Pattern.aml -> Runtime.value -> Runtime.value list option Runtime.toplevel

val match_op_pattern :
  Pattern.aml list -> Pattern.aml option ->
  Runtime.value list -> Jdg.ty option ->
  Runtime.value list option Runtime.comp
