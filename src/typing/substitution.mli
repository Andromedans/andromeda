type t

val empty : t

val lookup : Mlty.meta -> t -> Mlty.ty option

val apply : t -> Mlty.ty -> Mlty.ty

val freshen_metas : Mlty.meta list -> t * Mlty.meta list

val from_lists : Mlty.meta list -> Mlty.ty list -> t

val add : Mlty.meta -> Mlty.ty -> t -> t option

val gather_known : t -> Mlty.MetaSet.t

