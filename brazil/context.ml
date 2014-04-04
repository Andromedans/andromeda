(** Context with hints. *)

type t = {
  vars : Syntax.ty list ;
  names : Syntax.name list ;
  hints : (Syntax.term * Syntax.term * Syntax.ty) list
}

let add_var x t ctx =
  { ctx with
    vars = t :: ctx.vars ;
    names = x :: ctx.names }
    
let add_hint e1 e2 t ctx =
  { ctx with
    hints = (e1, e2, t) :: ctx.hints }

let lookup_var x {vars=lst} =
  try
    List.nth lst x
  with
    | Failure _ -> Error.internal "invalid de Bruijn index"
