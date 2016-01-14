
(** [mk_abstractable ctx xs] prepares context [ctx] for abstracting atoms [xs].
    It returns a context [ctx'], atoms [ys] and terms [es],
    with [ctx'] the context where the atoms [ys] blocking abstraction in [ctx] have been instantiated  by [es]. *)
val mk_abstractable : loc:Location.t -> Context.t -> Name.atom list ->
  (Context.t * Name.atom list * Tt.term list) Value.result

(** [context_abstract ctx xs ts] computes [mk_abstractable ctx xs],
    and abstracts the result by [xs] and [ts]. *)
val context_abstract : loc:Location.t -> Context.t -> Name.atom list -> Tt.ty list ->
  (Context.t * Name.atom list * Tt.term list) Value.result


(** Match a value against a pattern. Matches are returned in order of decreasing de bruijn index. *)
val match_pattern : Syntax.pattern -> Value.value -> Value.value list option Value.result

val multimatch_pattern : Syntax.pattern list -> Value.value list -> Value.value list option Value.result

