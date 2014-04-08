(** Context with hints. *)

type declaration =
  | Parameter of Syntax.ty
  | Definition of Syntax.ty * Syntax.term

type hint =
  | Equation of Syntax.term * Syntax.term * Syntax.ty 
  | Rewrite of Syntax.term * Syntax.term * Syntax.ty

type t = {
  decls : declaration list ;
  names : Syntax.name list ;
  hints : hint list
}

let empty = { decls = [] ; names = [] ; hints = [] }

let names {names=lst} = lst

let add_var x t ctx =
  { ctx with
    decls = Parameter t :: ctx.decls ;
    names = x :: ctx.names }
    
let add_def x t e ctx =
  { ctx with
    decls = Definition (t, e) :: ctx.decls ;
    names = x :: ctx.names }
    
let add_equation e1 e2 t ctx =
  { ctx with
    hints = Equation (e1, e2, t) :: ctx.hints }

let add_rewrite e1 e2 t ctx =
  { ctx with
    hints = Rewrite (e1, e2, t) :: ctx.hints }

let lookup_var x {decls=lst} =
  try begin
    match List.nth lst x with
      | Parameter t -> t
      | Definition (t, _) -> t
  end
  with
    | Failure _ -> Error.impossible "invalid de Bruijn index"

let print {decls=ds; names=xs} =
  let rec loop ds xs =
    match ds, xs with
      | [], [] -> ()
      | d::ds, x::xs ->
        loop ds xs ;
        begin match d with
          | Parameter t -> Format.printf "assume %s : %t@\n" x (Print.ty xs t)
          | Definition (t, e) -> Format.printf "define %s : %t := %t@\n" x (Print.ty xs t) (Print.term xs e)
        end
      | [], _::_ -> Error.impossible "fewer declarations than names in context"
      | _::_, [] -> Error.impossible "fewer names than declarations in context"
  in
    loop ds xs ;
    Format.printf "@."
