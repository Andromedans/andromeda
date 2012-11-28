(** A context is represented as an associative list which maps a variable [x] to a pair
   [(t,e)] where [t] is its type and [e] is its value (optional).
*)
type context = {
  names : string list ;
  defs : (Syntax.expr option) list ;
  tys : Syntax.expr list
}

(** Handling of contexts. *)

let empty_context = {
  names = [] ;
  defs = [] ;
  tys = []
}
    
(** [lookup_ty k ctx] returns the type of [k] in context [ctx]. *)
let lookup_ty k {tys=lst} = Syntax.shift (k+1) (List.nth lst k)

let lookup_definition k {defs=lst} = 
  match List.nth lst k with
    | None -> None
    | Some e -> Some (Syntax.shift (k+1) e)

(** [extend x t ctx] returns [ctx] extended with variable [x] of type [t],
    whereas [extend x t ~value:e ctx] returns [ctx] extended with variable [x]
    of type [t] and assigned value [e]. *)
let extend x t ?definition ctx =
  { names = x :: ctx.names ;
    defs = definition :: ctx.defs ;
    tys = t :: ctx.tys }

