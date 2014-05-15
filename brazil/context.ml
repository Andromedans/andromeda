(** Context with hints. *)

type hint = int * Pattern.ty * Pattern.term * Pattern.term

type entry =
  | Variable of Syntax.ty
  | Definition of Syntax.ty * Syntax.term
  | Equation of hint
  | Rewrite of hint

type t = {
  decls : entry list ;
  names : Syntax.name list
}

let print {decls=ds; names=xs} =
  let rec print_names ds xs =
    match ds, xs with
      | [], [] -> ()
      | (Variable t :: ds), x::xs ->
        print_names ds xs ;
        Format.printf "@[<hov 4>assume %s@;<1 -2>: %t@]@\n" x (Print.ty xs t)
      | (Definition (t, e) :: ds), x :: xs ->
        print_names ds xs ;
        Format.printf "@[<hov 4>define %s@;<1 -2>: %t@;<1 -2>:= %t@]@\n"
          x (Print.ty xs t) (Print.term xs e)
      | (Equation _ :: ds), xs ->
        print_names ds xs ;
        Format.printf "@[<hov 4>equation <pattern>@]@\n"
      | (Rewrite _ :: ds), xs ->
        print_names ds xs ;
        Format.printf "@[<hov 4>rewrite <pattern>@]@\n"
      | [], _::_ -> Error.impossible "fewer declarations than names in context"
      | _::_, [] -> Error.impossible "fewer names than declarations in context"
  in
    Format.printf "---vvv---@.";
    print_names ds xs ;
    Format.printf "---^^^---@."

let empty = { decls = [] ; names = [] }

let names {names=lst} = lst

let add_var x t ctx =
  { decls = Variable t :: ctx.decls ;
    names = x :: ctx.names }

let add_vars bnds ctx =
  let rec loop vars_added accum_ctx = function
    | []          -> accum_ctx
    | (x,t)::rest ->
        loop (vars_added+1)
             (add_var x (Syntax.shift_ty vars_added t) accum_ctx)
             rest
  in
    loop 0 ctx bnds

let for_J t x y p z ctx =
  let ctx_xy = add_vars [(x, t); (y, t)] ctx in
  let ctx_xyp =
    add_var
      p
      (Syntax.Paths
         (Syntax.shift_ty 2 t,  (* Weaken twice for x and y *)
          (Syntax.Var 0 (* x *), Position.nowhere),
          (Syntax.Var 1 (* y *), Position.nowhere)),
       Position.nowhere) ctx_xy
  and ctx_z = add_var z t ctx
  in
    ctx_xyp, ctx_z


let add_def x t e ctx =
  { decls = Definition (t, e) :: ctx.decls ;
    names = x :: ctx.names }

let add_equation h ctx =
  { decls = Equation h :: ctx.decls ;
    names = ctx.names }

let add_rewrite h ctx =
  { decls = Rewrite h :: ctx.decls ;
    names = ctx.names }

let lookup_var index {decls=ds} =
  let rec lookup k = function
    | [] -> Error.impossible "invalid de Bruijn index"
    | (Equation _ | Rewrite _) :: ds -> lookup k ds
    | (Variable t | Definition (t, _)) :: ds ->
        if k = 0
        then Syntax.shift_ty (index+1) t
        else lookup (k-1) ds
  in
    if index < 0 then Error.impossible "negative de Bruijn index" ;
    lookup index ds

let lookup_def index {decls=ds} =
  let rec lookup k = function
    | [] -> Error.impossible "invalid de Bruijn index"
    | (Equation _ | Rewrite _) :: ds -> lookup k ds
    | Variable _ :: ds ->
      if k = 0
      then None
      else lookup (k-1) ds
    | Definition (_, e) :: ds ->
      if k = 0
      then Some (Syntax.shift (index+1) e)
      else lookup (k-1) ds
  in
    if index < 0 then Error.impossible "negative de Bruijn index" ;
    lookup index ds

let equations {decls=lst} =
  let rec collect k = function
    | [] -> []
    | (Variable _ | Definition _) :: lst -> collect (k+1) lst
    | Rewrite _ :: lst -> collect k lst
    | Equation (j, pt, pe1, pe2) :: lst ->
      let pt = Pattern.shift_ty k 0 pt
      and pe1 = Pattern.shift k 0 pe1
      and pe2 = Pattern.shift k 0 pe2
      in
        (j, pt, pe1, pe2) :: (collect k lst)
  in
    collect 0 lst

let rewrites {decls=lst} =
  let rec collect k = function
    | [] -> []
    | (Variable _ | Definition _) :: lst -> collect (k+1) lst
    | Equation _ :: lst -> collect k lst
    | Rewrite (j, pt, pe1, pe2) :: lst ->
      let pt = Pattern.shift_ty k 0 pt
      and pe1 = Pattern.shift k 0 pe1
      and pe2 = Pattern.shift k 0 pe2
      in
        (j, pt, pe1, pe2) :: (collect k lst)
  in
    collect 0 lst

let append ctx1 ctx2 =
  {
    (* "backwards" because the contexts are stored backwards,
     * with the newest variable at the front of the list. *)
    decls = ctx2.decls @ ctx1.decls;
    names = ctx2.names @ ctx1.names;
  }

