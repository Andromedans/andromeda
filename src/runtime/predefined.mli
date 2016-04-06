val definitions : Input.toplevel list

val operation_equal : loc:Location.t -> Jdg.term -> Jdg.term -> Jdg.term option Runtime.comp

val operation_as_prod : loc:Location.t -> Jdg.term -> Jdg.term option Runtime.comp
val operation_as_eq : loc:Location.t -> Jdg.term -> Jdg.term option Runtime.comp

val as_list : loc:Location.t -> Runtime.value -> Runtime.value list
val mk_list : Runtime.value list -> Runtime.value

(** Wrappers for making tags *)
val from_option : Runtime.value option -> Runtime.value
val as_option : loc:Location.t -> Runtime.value -> Runtime.value option

