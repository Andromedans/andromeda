module ConstantMap = Name.IdentMap

type env = {
  constants : Tt.ty ConstantMap.t;
}

let empty = {
  constants = ConstantMap.empty;
}

type term = Term of Context.t * Tt.term * Tt.ty

type atom = JAtom of Context.t * Name.atom * Tt.ty

type ty = Ty of Context.t * Tt.ty

let typeof (Term (ctx, _, t)) =
  Ty (ctx, t)

let mk_atom ~loc ctx x =
  match Context.lookup_ty x ctx with
    | Some t -> JAtom (ctx,x,t)
    | None -> Error.impossible ~loc "Cannot make unknown atom judgement"

let atom_ty (JAtom (ctx,x,t)) =
  Ty (ctx,t)

let atom_term ~loc (JAtom (ctx,x,t)) =
  Term (ctx,Tt.mk_atom ~loc x,t)

let term_of_ty (Ty (ctx,Tt.Ty ({Tt.loc=loc;_} as t))) = Term (ctx,t,Tt.mk_type_ty ~loc)

let mk_term ctx e t = Term (ctx, e, t)

let mk_ty ctx t = Ty (ctx, t)

let ty_ty = Ty (Context.empty, Tt.typ)

let strengthen (Term (ctx,e,t)) =
  let hyps = Name.AtomSet.union (Tt.assumptions_term e) (Tt.assumptions_ty t) in
  let ctx = Context.restrict ctx hyps in
  Term (ctx,e,t)

let print_term ~penv ?max_level (Term (ctx, e, t)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hv>@[<hov>%t@]@;<1 -2>: @[<hov>%t@]@]"
              (Context.print ~penv ctx)
              (Print.char_vdash ())
              (Tt.print_term ~penv ~max_level:Level.highest e)
              (Tt.print_ty ~penv ~max_level:Level.highest t)

let print_ty ~penv ?max_level (Ty (ctx, t)) ppf =
  Print.print ?max_level ~at_level:Level.jdg ppf
              "%t%s @[<hov>%t@]@ type"
              (Context.print ~penv ctx)
              (Print.char_vdash ())
              (Tt.print_ty ~penv ~max_level:Level.highest t)

(** Environment *)
let constant_type c env =
  ConstantMap.find c env.constants

let add_constant c t env =
  {constants = ConstantMap.add c t env.constants}

(** Destructors *)
type 'a abstraction = atom * 'a

type shape =
  | Type
  | Atom of atom
  | Constant of Name.constant
  | Prod of ty abstraction
  | Lambda of term abstraction
  | Apply of term * term
  | Eq of term * term
  | Refl of term

let mk_fresh x (Ty (ctx,a)) =
  let y,ctx = Context.add_fresh ctx x a in
  ctx,y,JAtom (ctx,y,a)

let shape ~loc env (Term (ctx,e,t)) =
  match e.Tt.term with
    | Tt.Type -> Type

    | Tt.Atom x -> Atom (mk_atom ~loc:e.Tt.loc ctx x)

    | Tt.Constant c -> Constant c

    | Tt.Prod ((x,a),b) ->
      let ja = mk_ty ctx a in
      let ctx,y,jy = mk_fresh x ja in
      let b = Tt.unabstract_ty [y] b in
      let jb = mk_ty ctx b in
      Prod (jy,jb)

    | Tt.Lambda ((x,a),(e,b)) ->
      let ja = mk_ty ctx a in
      let ctx,y,jy = mk_fresh x ja in
      let b = Tt.unabstract_ty [y] b
      and e = Tt.unabstract [y] e in
      let je = mk_term ctx e b in
      Lambda (jy,je)


    | Tt.Apply (e1,((x,a),b),e2) ->
      let je2 = mk_term ctx e2 a in
      let prod = Tt.mk_prod_ty ~loc:e.Tt.loc x a b in
      let je1 = mk_term ctx e1 prod in
      Apply (je1,je2)

    | Tt.Eq (a,e1,e2) ->
      let je1 = mk_term ctx e1 a
      and je2 = mk_term ctx e2 a in
      Eq (je1,je2)

    | Tt.Refl (a,e) ->
      let e = mk_term ctx e a in
      Refl e

    | Tt.Bound _ -> Error.impossible ~loc:e.Tt.loc "Unbound variable in judgement"

let shape_ty ~loc env j = shape ~loc env (term_of_ty j)

(** Construct judgements *)
let form ~loc ~penv env = function
  | Type ->
    Term (Context.empty, Tt.mk_type ~loc, Tt.mk_type_ty ~loc)

  | Atom x -> atom_term ~loc x

  | Constant c ->
    let t = constant_type c env in
    Term (Context.empty,Tt.mk_constant ~loc c,t)

  | Prod ((JAtom (ctxa,x,a)),(Ty (ctxb,b))) ->
    let ctx = Context.join ~loc ~penv ctxb ctxa in
    let ctx = Context.abstract ~loc ~penv ctx x a in
    let b = Tt.abstract_ty [x] b in
    Term (ctx,Tt.mk_prod ~loc (Name.ident_of_atom x) a b,Tt.mk_type_ty ~loc)

  | Lambda ((JAtom (ctxa,x,a)),(Term (ctxe,e,b))) ->
    let ctx = Context.join ~loc ~penv ctxe ctxa in
    let ctx = Context.abstract ~loc ~penv ctx x a in
    let b = Tt.abstract_ty [x] b
    and e = Tt.abstract [x] e in
    let x = Name.ident_of_atom x in
    Term (ctx,Tt.mk_lambda ~loc x a e b,Tt.mk_prod_ty ~loc x a b)

  | Apply ((Term (ctx1,e1,t1) as j1), (Term (ctx2,e2,t2) as j2)) ->
    let ctx = Context.join ~loc ~penv ctx2 ctx1 in
    let Tt.Ty te1 = t1 in
    begin match te1.Tt.term with
      | Tt.Prod ((x,a),b) ->
        if Tt.alpha_equal_ty a t2
        then
          let out = Tt.instantiate_ty [e2] b in
          Term (ctx,Tt.mk_apply ~loc e1 x a b e2,out)
        else
          Error.impossible ~loc "cannot apply %t to %t: wrong argument type" (print_term ~penv j1) (print_term ~penv j2)
      | _ -> Error.impossible ~loc "cannot apply %t to %t: not a product" (print_term ~penv j1) (print_term ~penv j2)
    end

  | Eq ((Term (ctx1,e1,t1) as j1), (Term (ctx2,e2,t2) as j2)) ->
    let ctx = Context.join ~loc ~penv ctx2 ctx1 in
    if Tt.alpha_equal_ty t1 t2
    then
      Term (ctx, Tt.mk_eq ~loc t1 e1 e2, Tt.mk_type_ty ~loc)
    else
      Error.impossible ~loc "cannot consider %t == %t: different types" (print_term ~penv j1) (print_term ~penv j2)

  | Refl (Term (ctx,e,t)) ->
    Term (ctx,Tt.mk_refl ~loc t e,Tt.mk_eq_ty ~loc t e e)

let is_ty ~penv (Term (ctx,e,t) as j) =
  if Tt.alpha_equal_ty t Tt.typ
  then
    Ty (ctx,Tt.ty e)
  else
    Error.impossible ~loc:e.Tt.loc "%t is not a judgement that the term is a type." (print_term ~penv j)

let form_ty ~loc ~penv env s =
  is_ty ~penv (form ~loc ~penv env s)

