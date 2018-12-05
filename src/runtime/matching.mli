
(** Match a value against a pattern. Matches are returned in order of increasing de Bruijn index:
    if we match the pattern [(x,y,z)] against the value [("foo", "bar", "baz")], the list returned
    will be [["baz", "bar", "foo"]]. *)
val match_pattern : Pattern.aml -> Runtime.value -> Runtime.value list option Runtime.comp

(** Match a value against a pattern. Matches are returned in the order of increasing de Bruijn index. *)
val top_match_pattern : Pattern.aml -> Runtime.value -> Runtime.value list option Runtime.toplevel

(** [match_op_pattern ps p_out vs t_out] matches patterns [ps] against values [vs] and
    the optional pattern [p_out] against the optional type [t_out]. *)
val match_op_pattern :
  loc:Location.t ->
  Pattern.aml list -> Pattern.is_type option ->
  Runtime.value list -> Jdg.is_type_abstraction option ->
  Runtime.value list option Runtime.comp
