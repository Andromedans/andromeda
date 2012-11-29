(** A context is represented as an associative list which maps a variable [x] to a pair
   [(t,e)] where [t] is its type and [e] is its value (optional).
*)

type declaration = 
  | Parameter of Syntax.expr
  | Definition of Syntax.expr * Syntax.expr

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
    | Parameter t | Definition (t, _) -> Syntax.shift (k+1) t

let lookup_definition k {decls=lst;names=names} = 
  match List.nth lst k with
    | Definition (_, e) -> Some (Syntax.shift (k+1) e)
    | Parameter _ -> None

let add_parameter x t ctx =
    { names = x :: ctx.names ;
      decls = Parameter t :: ctx.decls }

let add_definition x t e ctx =
    { names = x :: ctx.names ;
      decls = Definition (t, e) :: ctx.decls }

let chop k ctx =
  let rec chop lst = function
    | 0 -> lst
    | k -> chop (List.tl lst) (k - 1)
  in
    { names = chop ctx.names k ; decls = chop ctx.decls k }
