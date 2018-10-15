
(** Match a value against a pattern. Matches are returned in order of decreasing de Bruijn index. *)
val match_pattern : Pattern.aml -> Runtime.value -> Runtime.value list option Runtime.comp

(** Match a value against a pattern. Matches are returned in the order of decreasing de Bruijn index. *)
val top_match_pattern : Pattern.aml -> Runtime.value -> Runtime.value list option Runtime.toplevel

(** [match_op_pattern ps p_out vs t_out] matches patterns [ps] against values [vs] and
    the optional pattern [p_out] against the optional type [t_out]. *)
val match_op_pattern :
  Pattern.aml list -> Pattern.is_type option ->
  Runtime.value list -> Runtime.is_type_abstraction option ->
  (Name.ident * Runtime.value) list option Runtime.comp
