type t

val empty : t

val lookup : Amltype.meta -> t -> Amltype.ty option

val apply : t -> Amltype.ty -> Amltype.ty

val freshen_metas : Amltype.meta list -> t * Amltype.meta list

val from_lists : Amltype.meta list -> Amltype.ty list -> t

val add : Amltype.meta -> Amltype.ty -> t -> t option

val gather_known : t -> Amltype.MetaSet.t

