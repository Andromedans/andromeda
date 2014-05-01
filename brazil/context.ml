(** Context with hints. *)

type declaration =
  | Parameter of Syntax.ty
  | Definition of Syntax.ty * Syntax.term

(** A hint is stored as a quadruple [(k, t, e1, e2)], meaning
    that it is possible to inhabit [Syntax.Id (t', e1', e2')]
    by matching [t = t'], [e1 = e1'] and [e2 = e2'] and instantiating
    variables [0, ..., k-1].
*)
type hint =
  | Equation of (int * Syntax.ty * Syntax.term * Syntax.term)
  | Rewrite of (int * Syntax.ty * Syntax.term * Syntax.term)

type t = {
  decls : declaration list ;
  names : Syntax.name list ;
  hints : hint list
}

let print {decls=ds; hints=hs; names=xs} =
  let rec print_names ds xs =
    match ds, xs with
      | [], [] -> ()
      | d::ds, x::xs ->
        print_names ds xs ;
        begin match d with
          | Parameter t ->
              Format.printf "@[<hov 4>assume %s@;<1 -2>: %t@]@\n" x (Print.ty xs t)
          | Definition (t, e) ->
              Format.printf "@[<hov 4>define %s@;<1 -2>: %t@;<1 -2>:= %t@]@\n"
                x (Print.ty xs t) (Print.term xs e)
        end
      | [], _::_ -> Error.impossible "fewer declarations than names in context"
      | _::_, [] -> Error.impossible "fewer names than declarations in context"
  in
  let rec metanames j = if j <= 0 then xs else ("?" ^ string_of_int (j-1)) :: metanames (j-1) in
  let print_hints =
    List.iter (function
      | Rewrite (k, t, e1, e2) ->
        Format.printf "rewrite (_ :: %t)@\n"
          (Print.ty (metanames k) (Syntax.Id (t, e1, e2), Position.nowhere))
      | Equation (k, t, e1, e2) ->
        Format.printf "equation (_ :: %t)@\n"
          (Print.ty (metanames k) (Syntax.Id (t, e1, e2), Position.nowhere))
    )
  in
    print_names ds xs ;
    print_hints hs ;
    Format.printf "@."


let empty = { decls = [] ; names = [] ; hints = [] }

let names {names=lst} = lst

let shift_declaration delta = function
  | Parameter ty1 ->
      Parameter( Syntax.shift_ty delta ty1 )
  | Definition(ty1, term1) ->
      Definition( Syntax.shift_ty delta ty1,
                  Syntax.shift delta term1 )

let shift_hint delta = function
  | Equation (k, t, e1, e2) ->
    Equation (k, Syntax.shift_ty ~bound:k delta t,
                 Syntax.shift ~bound:k delta e1,
                 Syntax.shift ~bound:k delta e2)
  | Rewrite (k, t, e1, e2) ->
    Rewrite (k, Syntax.shift_ty ~bound:k delta t,
                Syntax.shift ~bound:k delta e1,
                Syntax.shift ~bound:k delta e2)

let add_var x t ctx =
  {
    decls = Parameter t :: ctx.decls ;
    hints = List.map (shift_hint 1) ctx.hints;
    names = x :: ctx.names;
  }

let add_vars bnds ctx =
  let rec loop vars_added accum_ctx = function
    | []          -> accum_ctx
    | (x,t)::rest ->
        loop (vars_added+1)
             (add_var x (Syntax.shift_ty vars_added t) accum_ctx)
             rest
  in
     loop 0 ctx bnds

let add_def x t ((_,loc) as e) ctx =
  let h = Rewrite (0, Syntax.shift_ty 1 t, (Syntax.Var 0, loc), Syntax.shift 1 e) in
  {
    decls = Definition (t, e) :: ctx.decls ;
    hints = h :: List.map (shift_hint 1) ctx.hints ;
    names = x :: ctx.names;
  }

(** We always store all hints strongly normalized. Then we try
    to apply them, we strongly normalize the target as well. *)
let add_equation (_, loc) t ctx =
  match Hint.prepare t with
    | Some (k, t, e1, e2) ->
      { ctx with hints = Equation (k, t, e1, e2) :: ctx.hints }
    | None ->
      Error.typing ~loc "this expression has type %t but should be a universally quantified equality"
        (Print.ty ctx.names t)

let add_rewrite (_, loc) t ctx =
  match Hint.prepare t with
    | Some (k, t, e1, e2) ->
      { ctx with hints = Rewrite (k, t, e1, e2) :: ctx.hints }
    | None ->
      Error.typing ~loc "this expression has type %t but should be a universally quantified equality"
        (Print.ty ctx.names t)

let lookup_var index {decls=lst} =
  try begin
    let inserted_ty =
      match List.nth lst index with
      | Parameter t       -> t
      | Definition (t, _) -> t  in
    (* Return the classifier relative to *this* context, not
       the context where we inserted the type.  (Unlike hints,
       we don't shift these inserted types each time a new
       variable is added to the context.)
     *)
    Syntax.shift_ty (index+1) inserted_ty
  end
  with
    | Failure _ -> Error.impossible "invalid de Bruijn index"

let lookup_equation t e1 e2 ctx =
  let t = Norm.ty t
  and e1 = Norm.term e1
  and e2 = Norm.term e2 in
    List.exists
      (function Equation h | Rewrite h ->
        Hint.instantiate h t e1 e2 || Hint.instantiate h t e2 e1)
      ctx.hints

let lookup_rewrite t e1 ctx =
  let t = Norm.ty t
  and e1 = Norm.term e1 in
  let rec search = function
    | [] -> None
    | Equation _ :: lst -> search lst
    | Rewrite h :: lst ->
        begin match Hint.rewrite h t e1  with
          | None -> search lst
          | Some _ as e2 -> e2
        end
  in
    search ctx.hints

let append ctx1 ctx2 =
  let delta = List.length ctx2.decls in
  {
    decls = ctx1.decls @ ctx2.decls;
    hints = List.map (shift_hint delta) ctx1.hints @ ctx2.hints;
    names = ctx1.names @ ctx2.names;
  }

