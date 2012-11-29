(** A context is represented as an associative list which maps a variable [x] to a pair
   [(t,e)] where [t] is its type and [e] is its value (optional).
*)

type declaration = 
  | Parameter of Syntax.expr
  | Value of Value.value
  | Definition of Syntax.expr * Syntax.expr * Value.value

type context = {
  names : string list ;
  decls : declaration list
}

let empty_context = {
  names = [] ;
  decls = []
}
    
(** [lookup_ty k ctx] returns the type of [k] in context [ctx]. *)
let lookup_ty k {decls=lst} =
  match List.nth lst k with
    | Parameter t | Definition (t, _, _) -> Syntax.shift (k+1) t
    | Value _ -> assert false

let lookup_definition k {decls=lst} = 
  match List.nth lst k with
    | Definition (_, e, _) -> Some (Syntax.shift (k+1) e)
    | Value _ | Parameter _ -> None

let lookup_value k {decls=lst} = 
  match List.nth lst k with
    | Value v | Definition (_, _, v) -> Some (Value.shift (k+1) v)
    | Parameter _ -> None

let add_parameter x t ctx =
    { names = x :: ctx.names ;
      decls = Parameter t :: ctx.decls }

let add_value v ctx =
  { names = "_" :: ctx.names ;
    decls = Value v :: ctx.decls }

let add_definition x t d v ctx =
    { names = x :: ctx.names ;
      decls = Definition (t, d, v) :: ctx.decls }
