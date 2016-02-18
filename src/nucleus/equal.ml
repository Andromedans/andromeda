(** Equality checking and weak-head-normal-forms *)

(** Notation for the monads bind *)

module AtomSet = Name.AtomSet

module Monad = struct
  type state = AtomSet.t

  let empty = AtomSet.empty

  type 'a t =
    { k : 'r. ('a -> state -> 'r Value.comp) -> state -> 'r Value.comp }

  let return x =
    { k = fun c s -> c x s }

  let (>>=) m f =
    { k = fun c s -> m.k (fun x s -> (f x).k c s) s }

  (* lift : 'a Value.comp -> 'a t *)
  let lift m =
    { k = fun c s -> Value.bind m (fun x -> c x s) }

  let modify f =
    { k = fun c s -> c () (f s) }

  let add_hyps hyps = modify (AtomSet.union hyps)

  let context_abstract ~loc ctx y t =
    lift Value.lookup_penv >>= fun penv ->
    let ctx = Context.abstract ~penv ~loc ctx y t in
    modify (fun hyps -> AtomSet.remove y hyps) >>= fun () ->
    return ctx

  let run m =
    m.k (fun x s -> Value.return (x,s)) empty
end

module Opt = struct
  type state = Monad.state

  type 'a opt =
    { k : 'r. ('a -> state -> 'r Value.comp) -> (state -> 'r Value.comp) -> state -> 'r Value.comp }

  let return x =
    { k = fun sk _ s -> sk x s }

  let (>?=) m f =
    { k = fun sk fk s -> m.k (fun x s -> (f x).k sk fk s) fk s }

  let unfailing (m : 'a Monad.t) : 'a opt =
    { k = fun sk _ s -> m.Monad.k sk s }

  let fail =
    { k = fun _ fk s -> fk s }

  let locally (m : 'a opt) : ('a*state) opt =
    { k = fun sk fk s -> m.k (fun x s' -> sk (x,s') (AtomSet.union s s')) fk Monad.empty }

  let add_abstracting ~loc x j m =
    { k = fun sk fk s ->
          Value.add_abstracting ~loc x j (fun ctx z -> (m ctx z).k (fun y s' -> (sk y s')) fk s) }

  let run m =
    m.k (fun x s -> Value.return (Some (x,s))) (fun _ -> Value.return None) AtomSet.empty
end

let (>>=) = Monad.(>>=)

let (>?=) = Opt.(>?=)

let (>!=) m f = (Opt.unfailing m) >?= f

let context_multiabstract ~loc ctx yts =
  let rec fold ctx = function
    | [] -> Monad.return ctx
    | (y,t)::yts ->
      Monad.context_abstract ~loc ctx y t >>= fun ctx ->
      fold ctx yts
  in
  fold ctx yts

let list_combine3 =
  let rec fold acc l1 l2 l3 = match l1,l2,l3 with
    | [],[],[] -> List.rev acc
    | x1::l1, x2::l2, x3::l3 -> fold ((x1,x2,x3)::acc) l1 l2 l3
    | _,_,_ -> raise (Invalid_argument "list_combine3")
  in
  fun l1 l2 l3 -> fold [] l1 l2 l3

(** Compare two types *)
let rec equal ctx ({Tt.loc=loc1;_} as e1) ({Tt.loc=loc2;_} as e2) t =
  Monad.lift Value.print_term >!= fun pte ->
  Monad.lift Value.print_ty >!= fun pty ->
  if Tt.alpha_equal e1 e2
  then
    Opt.return ctx
  else
    Monad.lift (Value.operation_equal
        (Value.mk_term (Jdg.mk_term ctx e1 t))
        (Value.mk_term (Jdg.mk_term ctx e2 t))) >!= fun v ->
    let loc = loc1 in
    match Value.as_option ~loc v with
      | None -> Opt.fail
      | Some v ->
        let Jdg.Term (ctxeq,eq,teq) = Value.as_term ~loc v in
        Monad.lift Value.lookup_penv >!= fun penv ->
        let ctx = Context.join ~penv ~loc ctx ctxeq in
        Monad.add_hyps (Tt.assumptions_term eq) >!= fun () ->
        let tgoal = Tt.mk_eq_ty ~loc t e1 e2 in
        equal_ty ctx teq tgoal

and equal_ty ctx (Tt.Ty t1) (Tt.Ty t2) = equal ctx t1 t2 Tt.typ

(** Compare signatures structurally *)
let equal_signature ~loc ctx (s1,shares1) (s2,shares2) =
  if Name.eq_ident s1 s2
  then
    Monad.lift (Value.lookup_signature ~loc s1) >!= fun s_def ->
    (* [yts] abstracting data (types are instantiated using constraints from shares1)
       [hyps] prove that the previous constraints were respectively equal
          (and therefore that a type instantiated with shares1 is equal to the same instantiated with shares2)
       [vs]  atoms of [ys1] and instantiated terms from [shares1] used to instantiate types
       [ys1] atoms with type instantiated using shares1
       [ys2] atoms with type instantiated using shares2
    *)
    let rec fold ctx hyps yts vs ys1 ys2 = function
      | [] ->
        context_multiabstract ~loc ctx yts >!= fun ctx ->
        Opt.return ctx
      | ((_,_,t),(Tt.Inl x),(Tt.Inl _))::rem ->
        let t = Tt.instantiate_ty vs t in
        let jt = Jdg.mk_ty ctx t in
        Opt.add_abstracting ~loc x jt (fun ctx y ->
        let y1 = Tt.mk_atom ~loc y in
        let y2 = Tt.mention_atoms hyps y1 in
        fold ctx hyps ((y,t)::yts) (y1::vs) (y1::ys1) (y2::ys2) rem)
      | ((_,_,t),(Tt.Inr e1),(Tt.Inr e2))::rem ->
        let t = Tt.instantiate_ty vs t
        and e1 = Tt.instantiate ys1 e1
        and e2 = Tt.instantiate ys2 e2 in
        (* TODO: this could be slightly more granular by using only the hyps relevant to the assumptions of t *)
        let e2 = Tt.mention_atoms hyps e2 in
        Opt.locally (equal ctx e1 e2 t) >?= fun (ctx,hyps') ->
        let hyps = AtomSet.union hyps hyps' in
        fold ctx hyps yts (e1::vs) ys1 ys2 rem
      | (_,Tt.Inl _,Tt.Inr _)::_ | (_,Tt.Inr _,Tt.Inl _)::_ -> Opt.fail
    in
    fold ctx AtomSet.empty [] [] [] [] (list_combine3 s_def shares1 shares2)
  else
    Opt.fail

(** Compare structures structurally *)
(* TODO: compare constraints and fields simultaneously? *)
let equal_structure ~loc ctx ((s1,_) as str1) ((s2,_) as str2) =
  Opt.locally (equal_signature ~loc ctx s1 s2) >?= fun (ctx,hyps) ->
  Monad.lift (Value.lookup_signature ~loc (fst s1)) >!= fun s_def ->
  (* [vs] are used to instantiate the type *)
  let rec fold ctx hyps vs = function
    | [] ->
      Opt.return ctx
    | (_,Tt.Shared e,Tt.Shared _)::rem -> (* already checked by equal_signature *)
      fold ctx hyps (e::vs) rem
    | ((_,_,t),Tt.Explicit e1,Tt.Explicit e2)::rem ->
      let t = Tt.instantiate_ty vs t in
      let e2 = Tt.mention_atoms hyps e2 in
      Opt.locally (equal ctx e1 e2 t) >?= fun (ctx,hyps') ->
      let hyps = AtomSet.union hyps hyps' in
      fold ctx hyps (e1::vs) rem
    | (_,Tt.Explicit _,Tt.Shared _)::_ | (_,Tt.Shared _,Tt.Explicit _)::_ -> Error.impossible ~loc "equal_structure: malformed structure"
  in
  fold ctx AtomSet.empty [] (list_combine3 s_def (Tt.struct_combine ~loc str1) (Tt.struct_combine ~loc str2))

(** Apply the appropriate congruence rule *)
let congruence ~loc ctx ({Tt.loc=loc1;_} as e1) ({Tt.loc=loc2;_} as e2) t =
  match e1.Tt.term, e2.Tt.term with

  | Tt.Atom x, Tt.Atom y ->
     if Name.eq_atom x y then Opt.return ctx
     else Opt.fail

  | Tt.Bound _, _ | _, Tt.Bound _ ->
     Error.impossible ~loc "deBruijn encountered in congruence"

  | Tt.Constant x, Tt.Constant y ->
     if Name.eq_ident x y then Opt.return ctx
     else Opt.fail

  | Tt.Lambda ((x,a1), (e1, t1)), Tt.Lambda ((_,a2), (e2, t2)) ->
    Opt.locally (equal_ty ctx a1 a2) >?= fun (ctx,hypsa) ->
    let ja = Jdg.mk_ty ctx a1 in
    Opt.add_abstracting ~loc x ja (fun ctx y ->
    let y' = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
    let e1 = Tt.unabstract [y] e1
    and t1 = Tt.unabstract_ty [y] t1
    and e2 = Tt.instantiate [y'] e2
    and t2 = Tt.instantiate_ty [y'] t2 in
    Opt.locally (equal_ty ctx t1 t2) >?= fun (ctx,hypst) ->
    let e2 = Tt.mention_atoms hypst e2 in
    equal ctx e1 e2 t1 >?= fun ctx ->
    Monad.context_abstract ~loc ctx y a1 >!= fun ctx ->
    Opt.return ctx)

  | Tt.Apply (h1, ((x,a1),b1), e1), Tt.Apply (h2, ((_,a2),b2), e2) ->
    Opt.locally (equal_ty ctx a1 a2) >?= fun (ctx,hypsa) ->
    Opt.locally (Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a1) (fun ctx y ->
      let y' = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
      let b1 = Tt.unabstract_ty [y] b1
      and b2 = Tt.instantiate_ty [y'] b2 in
      equal_ty ctx b1 b2 >?= fun ctx ->
      Monad.context_abstract ~loc ctx y a1 >!= fun ctx ->
      Opt.return ctx)) >?= fun (ctx,hypsb) ->
    let prod = Tt.mk_prod_ty ~loc x a1 b1 in
    let h2 = Tt.mention_atoms hypsb (Tt.mention_atoms hypsa h2) in
    equal ctx h1 h2 prod >?= fun ctx ->
    let e2 = Tt.mention_atoms hypsa e2 in
    equal ctx e1 e2 a1

  | Tt.Type, Tt.Type -> Opt.return ctx

  | Tt.Prod ((x,a1), b1), Tt.Prod ((_,a2), b2) ->
    Opt.locally (equal_ty ctx a1 a2) >?= fun (ctx,hypsa) ->
    Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a1) (fun ctx y ->
    let y' = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
    let b1 = Tt.unabstract_ty [y] b1
    and b2 = Tt.instantiate_ty [y'] b2 in
    equal_ty ctx b1 b2 >?= fun ctx ->
    Monad.context_abstract ~loc ctx y a1 >!= fun ctx ->
    Opt.return ctx)

  | Tt.Eq (u, d1, d2), Tt.Eq (u', d1', d2') ->
     Opt.locally (equal_ty ctx u u') >?= fun (ctx,hyps) ->
     equal ctx d1 (Tt.mention_atoms hyps d1') u >?= fun ctx ->
     equal ctx d2 (Tt.mention_atoms hyps d2') u

  | Tt.Refl (u, d), Tt.Refl (u', d') ->
     Opt.locally (equal_ty ctx u u') >?= fun (ctx,hyps) ->
     equal ctx d (Tt.mention_atoms hyps d') u

  | Tt.Signature s1, Tt.Signature s2 ->
    equal_signature ~loc ctx s1 s2

  | Tt.Structure str1, Tt.Structure str2 ->
    equal_structure ~loc ctx str1 str2

  | Tt.Projection (e1, s1, l1), Tt.Projection (e2, s2, l2) ->
    if Name.eq_ident l1 l2
    then
      Opt.locally (equal_signature ~loc ctx s1 s2) >?= fun (ctx,hyps) ->
      let t = Tt.mk_signature_ty ~loc s1 in
      let e2 = Tt.mention_atoms hyps e2 in
      equal ctx e1 e2 t
    else Opt.fail

  | (Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Apply _ |
     Tt.Type | Tt.Prod _ | Tt.Eq _ | Tt.Refl _ |
     Tt.Signature _ | Tt.Structure _ | Tt.Projection _), _ ->
     Opt.fail


let extensionality ~loc ctx e1 e2 (Tt.Ty t') =
  match t'.Tt.term with
  | Tt.Prod ((x, a), b) ->
     Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a) (fun ctx y ->
       let yt = Tt.mk_atom ~loc y in
       let e1' = Tt.mk_apply ~loc e1 x a b yt in
       let e2' = Tt.mk_apply ~loc e2 x a b yt in
       let b' = Tt.unabstract_ty [y] b in
       equal ctx e1' e2' b' >?= fun ctx ->
       Monad.context_abstract ~loc ctx y a >!= fun ctx ->
         Opt.return ctx)

  | Tt.Eq _ -> Opt.return ctx

  | Tt.Signature ((s,shares) as s') ->
    Monad.lift (Value.lookup_signature ~loc s) >!= fun s_def ->
    (* [es] instantiate types
       [projs] instantiate constraints *)
    let rec fold ctx hyps es projs = function
        | [] -> Opt.return ctx
        | ((l, _, t), Tt.Inl _) :: rem ->
          let t = Tt.instantiate_ty es t in
          let e1_proj = Tt.mk_projection ~loc:e1.Tt.loc e1 s' l in
          let e2_proj = Tt.mk_projection ~loc:e2.Tt.loc e2 s' l in
          let e2_proj = Tt.mention_atoms hyps e2_proj in
          Opt.locally (equal ctx e1_proj e2_proj t) >?= fun (ctx, hyps') ->
          let hyps = AtomSet.union hyps hyps' in
          fold ctx hyps (e1_proj :: es) (e1_proj :: projs) rem
        | (_,Tt.Inr e) :: rem ->
          let e = Tt.instantiate projs e in
          fold ctx hyps (e::es) projs rem
    in
    fold ctx AtomSet.empty [] [] (List.combine s_def shares)

  | Tt.Type | Tt.Atom _ | Tt.Constant _ | Tt.Lambda _ | Tt.Apply _
  | Tt.Refl _ | Tt.Structure _ | Tt.Projection _ ->
      Opt.fail

  | Tt.Bound _ ->
     Error.impossible ~loc "deBruijn encountered in extensionality"
                                  


(** Beta reduction of [Lambda ((x,a), (e, b))] applied to argument [e'],
    where [((x,a'), b')] is the typing annotation for the application.
    Returns the resulting expression. *)
let beta_reduce ~loc ctx (x,a) e b (_,a') b' e' =
  Opt.locally (equal_ty ctx a a') >?= fun (ctx,hypsa) ->
  Opt.locally (Opt.add_abstracting ~loc x (Jdg.mk_ty ctx a) (fun ctx y ->
    let y' = Tt.mention_atoms hypsa (Tt.mk_atom ~loc y) in
    let b = Tt.unabstract_ty [y] b
    and b' = Tt.instantiate_ty [y'] b' in
    equal_ty ctx b b' >?= fun ctx ->
    Monad.context_abstract ~loc ctx y a >!= fun ctx ->
    Opt.return ctx)) >?= fun (ctx,hypsb) ->
  let e' = Tt.mention_atoms hypsa e' in
  let e = Tt.instantiate [e'] e in
  let e = Tt.mention_atoms hypsb e in
  Opt.return (ctx,e)

let reduction_step ctx {Tt.term=e'; assumptions; loc} =
  match e' with
  | Tt.Apply (e1, (xts, t), e2) ->
     begin match e1.Tt.term with
           | Tt.Lambda (xus, (e', u)) ->
              beta_reduce ~loc ctx xus e' u xts t e2 >?= fun (ctx, e) ->
              Opt.return (ctx, Tt.mention assumptions e)
           | Tt.Atom _
           | Tt.Constant _
           | Tt.Apply _
           | Tt.Type
           | Tt.Prod _
           | Tt.Eq _
           | Tt.Refl _
           | Tt.Signature _
           | Tt.Structure _
           | Tt.Projection _ -> Opt.fail
           | Tt.Bound _ ->
              Error.impossible ~loc "de Bruijn encountered in an apply head in reduce"
     end

  | Tt.Projection (e, s, l) ->
    begin
      match e.Tt.term with
        | Tt.Structure ((s', _) as str) ->
          Opt.locally (equal_signature ~loc ctx s s') >?= fun (ctx,hyps) ->
          Monad.lift (Value.lookup_signature ~loc (fst s)) >!= fun s_def ->
          let e = Tt.field_value ~loc s_def str l in
          let e = Tt.mention_atoms hyps e in
          Opt.return (ctx, Tt.mention assumptions e)

       | Tt.Atom _
       | Tt.Constant _
       | Tt.Lambda _
       | Tt.Apply _
       | Tt.Type
       | Tt.Prod _
       | Tt.Eq _
       | Tt.Refl _
       | Tt.Signature _
       | Tt.Projection _ -> Opt.fail
       | Tt.Bound _ ->
          Error.impossible ~loc "de Bruijn encountered in a projection head in reduce"
     end

  | Tt.Constant _
  | Tt.Lambda _
  | Tt.Prod _
  | Tt.Atom _
  | Tt.Type
  | Tt.Eq _
  | Tt.Refl _
  | Tt.Signature _
  | Tt.Structure _ -> Opt.fail
  | Tt.Bound _ ->
     Error.impossible ~loc "de Bruijn encountered in reduce"


let as_eq_alpha (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t))) =
  match t' with
    | Tt.Eq (t, e1, e2) -> Monad.return (t, e1, e2)
    | _ ->
      Monad.lift Value.print_ty >>= fun pty ->
      Error.typing ~loc "this expression should be an equality, found@ %t"
          (pty t)

let as_eq (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Eq (t, e1, e2) -> Monad.return (ctx, t, e1, e2)
    | _ ->
      Monad.lift (Value.operation_as_eq (Value.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Value.as_option ~loc v with
        | None ->
          Monad.lift Value.print_ty >>= fun pty ->
          Error.typing ~loc "this expression should be an equality, found@ %t"
              (pty t)
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Value.as_term ~loc v in
          as_eq_alpha (Jdg.mk_ty ctxv tv) >>= fun (tv,e1,e2) ->
          if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
          then
            as_eq_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) >>= fun (t,e1,e2) ->
            Monad.lift Value.lookup_penv >>= fun penv ->
            let ctx = Context.join ~penv ~loc ctx ctxv in
            let hyps = Tt.assumptions_term ev in
            Monad.add_hyps hyps >>= fun () ->
            Monad.return (ctx,t,e1,e2)
          else
            Monad.lift (Value.print_ty) >>= fun pty ->
            Error.typing ~loc:ev.Tt.loc
                "this expression should be a witness of equality between %t and an equality"
                (pty t)
      end

let as_prod_alpha (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t))) =
  match t' with
    | Tt.Prod (xts,t) -> Monad.return (xts,t)
    | _ ->
      Monad.lift Value.print_ty >>= fun pty ->
      Error.typing ~loc "this expression should be a product, found@ %t"
          (pty t)

let as_prod (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Prod (xts,t) -> Monad.return (ctx, (xts,t))
    | _ ->
      Monad.lift (Value.operation_as_prod (Value.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Value.as_option ~loc v with
        | None ->
          Monad.lift Value.print_ty >>= fun pty ->
          Error.typing ~loc "this expression should be a product, found@ %t"
              (pty t)
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Value.as_term ~loc v in
          as_eq_alpha (Jdg.mk_ty ctxv tv) >>= fun (tv,e1,e2) ->
          if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
          then
            as_prod_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) >>= fun (xts,t) ->
            Monad.lift Value.lookup_penv >>= fun penv ->
            let ctx = Context.join ~penv ~loc ctx ctxv in
            let hyps = Tt.assumptions_term ev in
            Monad.add_hyps hyps >>= fun () ->
            Monad.return (ctx,(xts,t))
          else
            Monad.lift (Value.print_ty) >>= fun pty ->
            Error.typing ~loc:ev.Tt.loc
                "this expression should be a witness of equality between %t and a product"
                (pty t)
      end

let as_signature_alpha (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t))) =
  match t' with
    | Tt.Signature s -> Monad.return s
    | _ ->
      Monad.lift Value.print_ty >>= fun pty ->
      Error.typing ~loc "this expression should be a signature, found@ %t"
          (pty t)


let as_signature (Jdg.Ty (ctx, (Tt.Ty {Tt.term=t';loc;_} as t)) as jt) =
  match t' with
    | Tt.Signature s -> Monad.return (ctx, s)
    | _ ->
      Monad.lift (Value.operation_as_signature (Value.mk_term (Jdg.term_of_ty jt))) >>= fun v ->
      begin match Value.as_option ~loc v with
        | None ->
          Monad.lift Value.print_ty >>= fun pty ->
          Error.typing ~loc "this expression should be a signature, found@ %t"
              (pty t)
        | Some v ->
          let Jdg.Term (ctxv,ev,tv) = Value.as_term ~loc v in
          as_eq_alpha (Jdg.mk_ty ctxv tv) >>= fun (tv,e1,e2) ->
          if Tt.alpha_equal_ty tv Tt.typ && Tt.alpha_equal_ty t (Tt.ty e1)
          then
            as_signature_alpha (Jdg.mk_ty ctxv (Tt.ty e2)) >>= fun xts ->
            Monad.lift Value.lookup_penv >>= fun penv ->
            let ctx = Context.join ~penv ~loc ctx ctxv in
            let hyps = Tt.assumptions_term ev in
            Monad.add_hyps hyps >>= fun () ->
            Monad.return (ctx,xts)
          else
            Monad.lift (Value.print_ty) >>= fun pty ->
            Error.typing ~loc:ev.Tt.loc
                "this expression should be a witness of equality between %t and a signature"
                (pty t)
      end

