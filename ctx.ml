(** Handling of contexts. *)
    
(** A context is represented as an associative list which maps a variable [x] to a pair
   [(t,e)] where [t] is its type and [e] is its value (optional).
*)
type context = (Syntax.variable * (Syntax.expr * Syntax.expr option)) list

(** [lookup_ty x ctx] returns the type of [x] in context [ctx]. *)
let lookup_ty x ctx = fst (List.assoc x ctx)

(** [lookup_ty x ctx] returns the value of [x] in context [ctx], or [None] 
    if [x] has no assigned value. *)
let lookup_value x ctx = snd (List.assoc x ctx)

(** [extend x t ctx] returns [ctx] extended with variable [x] of type [t],
    whereas [extend x t ~value:e ctx] returns [ctx] extended with variable [x]
    of type [t] and assigned value [e]. *)
let extend x t ?value ctx = (x, (t, value)) :: ctx


