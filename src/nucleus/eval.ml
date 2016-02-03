(** Evaluation of computations *)

(** Notation for the monadic bind *)
let (>>=) = Value.bind

(** A filter that verifies the result is a term. *)
let as_term ~loc v =
  let e = Value.as_term ~loc v in
    Value.return e

(** Returns the atom with its natural type in [ctx] *)
let as_atom ~loc v =
  as_term ~loc v >>= fun (Jdg.Term (ctx,e,t) as j) ->
  match e.Tt.term with
    | Tt.Atom x ->
      begin match Context.lookup_ty x ctx with
        | Some t -> Value.return (ctx,x,t)
        | None ->
          Value.lookup_penv >>= fun penv ->
          Error.impossible ~loc "got an atom judgement %t but the atom is not in the context" (Jdg.print_term ~penv j)
      end
    | _ -> Value.print_term >>= fun print_term ->
      Error.runtime ~loc "expected an atom but got %t" (print_term e)

let as_handler ~loc v =
  let e = Value.as_handler ~loc v in
  Value.return e

let as_ref ~loc v =
  let e = Value.as_ref ~loc v in
  Value.return e

let as_list ~loc v =
  let lst = Value.as_list ~loc v in
  Value.return lst


(** Evaluate a computation -- infer mode. *)
let rec infer (c',loc) =
  match c' with
    | Syntax.Bound i ->
       Value.lookup_bound ~loc i

    | Syntax.Type ->
       let e = Tt.mk_type ~loc in
       let t = Tt.mk_type_ty ~loc in
       let et = Jdg.mk_term Context.empty e t in
       Value.return_term et

    | Syntax.Function (x, c) ->
       let f v =
         Value.add_bound x v
           (infer c)
       in
       Value.return_closure f

    | Syntax.Rec (f, x, c) ->
       let rec g v =
         Value.return_closure g >>= fun closed ->
         Value.add_bound f closed
         (Value.add_bound x v
         (infer c))
       in
       Value.return_closure g

    | Syntax.Data (t, cs) ->
       let rec fold vs = function
         | [] ->
            let vs = List.rev vs in
            let v = Value.mk_tag t vs in
            Value.return v
         | c :: cs ->
            infer c >>= fun v ->
            fold (v :: vs) cs
       in
       fold [] cs

    | Syntax.Nil ->
       Value.return Value.list_nil

    | Syntax.Cons (c1, c2) ->
       infer c1 >>= fun v1 ->
       infer c2 >>= as_list ~loc >>= fun lst ->
       Value.return (Value.list_cons v1 lst)

    | Syntax.Tuple cs ->
      let rec fold vs = function
        | [] -> Value.return (Value.mk_tuple (List.rev vs))
        | c :: cs -> (infer c >>= fun v -> fold (v :: vs) cs)
      in
      fold [] cs

    | Syntax.Handler {Syntax.handler_val; handler_ops; handler_finally} ->
        let handler_val =
          begin match handler_val with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~loc handler_val v
            in
            Some f
          end
        and handler_ops = Name.IdentMap.mapi (fun op cases ->
            let f (vs,cont) =
              Value.set_continuation cont
              (multimatch_cases ~loc op cases vs)
            in
            f)
          handler_ops
        and handler_finally =
          begin match handler_finally with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~loc handler_finally v
            in
            Some f
          end
        in
        Value.return_handler handler_val handler_ops handler_finally

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Value.perform op vs
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.With (c1, c2) ->
     infer c1 >>= as_handler ~loc >>= fun h ->
     Value.handle_result h (infer c2)

  | Syntax.Let (xcs, c) ->
     let_bind xcs (infer c)

  | Syntax.Ref c ->
     infer c >>= fun v ->
     Value.mk_ref v

  | Syntax.Lookup c ->
     infer c >>= as_ref ~loc >>= fun x ->
     Value.lookup_ref x

  | Syntax.Update (c1, c2) ->
     infer c1 >>= as_ref ~loc >>= fun x ->
     infer c2 >>= fun v ->
     Value.update_ref x v >>= fun () ->
     Value.return_unit

  | Syntax.Sequence (c1, c2) ->
     infer c1 >>= fun _ ->
     (* XXX is it a good idea to ignore the value?
        Maybe a warning would be nice when the value is not unit. *)
     infer c2

  | Syntax.Assume ((x, t), c) ->
     check_ty t >>= fun t ->
     Value.add_free ~loc x t (fun _ _ ->
       infer c)

  | Syntax.Where (c1, c2, c3) ->
    infer c2 >>= as_atom ~loc >>= fun (ctxa, a, ta) ->
    infer c1 >>= as_term ~loc >>= fun (Jdg.Term (ctx, e1, t1)) ->
    Value.lookup_penv >>= fun penv ->
    let ctx = Context.join ~penv ~loc ctxa ctx in
    check c3 (Jdg.mk_ty ctx ta) >>= fun (ctx, e2) ->
    let ctx_s = Context.substitute ~penv ~loc a (ctx,e2,ta) in
    let te_s = Tt.substitute [a] [e2] e1 in
    let ty_s = Tt.substitute_ty [a] [e2] t1 in
    let j_s = Jdg.mk_term ctx_s te_s ty_s in
    Value.return_term j_s

  | Syntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases

  | Syntax.Reduce c ->
     infer c >>= as_term ~loc >>= fun (Jdg.Term (ctx, e, t)) ->
     Equal.Opt.run (Equal.reduce_step ctx e) >>=
       begin function
         | Some ((ctx, e'), hyps) ->
            let eq = Tt.mk_refl ~loc t e in
            let eq = Tt.mention_atoms hyps eq in
            let teq = Tt.mk_eq_ty ~loc t e e' in
            let eqj = Jdg.mk_term ctx eq teq in
            Value.return (Value.from_option (Some (Value.mk_term eqj)))
         | None -> Value.return (Value.from_option None)
       end

  | Syntax.External s ->
     begin match External.lookup s with
       | None -> Error.runtime ~loc "unknown external %s" s
       | Some v -> v loc
     end

  | Syntax.Typeof c ->
    (* In future versions this is going to be a far less trivial computation,
       as it might actually fail when there is no way to name a type with a term. *)
    infer c >>= as_term ~loc >>= fun j ->
    Value.return_term (Jdg.term_of_ty (Jdg.typeof j))

  | Syntax.Ascribe (c1, c2) ->
     check_ty c2 >>= fun (Jdg.Ty (_,t') as t) ->
     check c1 t >>= fun (ctx, e) ->
     let j = Jdg.mk_term ctx e t' in
     Value.return_term j

  | Syntax.Constant x ->
    begin Value.lookup_constant x >>= function
      | Some t ->
         let e = Tt.mk_constant ~loc x in
         let eu = Jdg.mk_term Context.empty e t in
         Value.return_term eu
      | None -> Error.impossible ~loc "unknown constant %t during evaluation"
                                 (Name.print_ident x)
    end

  | Syntax.Lambda (x,u,c) ->
     infer_lambda ~loc x u c

  | Syntax.Apply (c1, c2) ->
    infer c1 >>= begin function
      | Value.Term j ->
        apply ~loc j c2
      | Value.Closure f ->
        infer c2 >>= fun v ->
        Value.apply_closure f v
      | Value.Handler _ | Value.Tag _ | Value.List _ | Value.Tuple _ |
        Value.Ref _ | Value.String _ as h ->
        Error.runtime ~loc "cannot apply %s" (Value.name_of h)
    end

  | Syntax.Prod (x,u,c) ->
    infer_prod ~loc x u c

  | Syntax.Eq (c1, c2) ->
     infer c1 >>= as_term ~loc:(snd c1) >>= fun (Jdg.Term (ctx, e1, t1')) ->
     let t1 = Jdg.mk_ty ctx t1' in
     check c2 t1 >>= fun (ctx, e2) ->
     let eq = Tt.mk_eq ~loc t1' e1 e2 in
     let typ = Tt.mk_type_ty ~loc in
     let j = Jdg.mk_term ctx eq typ in
     Value.return_term j

  | Syntax.Refl c ->
     infer c >>= as_term ~loc:(snd c) >>= fun (Jdg.Term (ctxe, e, t)) ->
     let e' = Tt.mk_refl ~loc t e
     and t' = Tt.mk_eq_ty ~loc t e e in
     let et' = Jdg.mk_term ctxe e' t' in
     Value.return_term et'

  | Syntax.Signature s ->
     let j = Jdg.mk_term Context.empty (Tt.mk_signature ~loc s) (Tt.mk_type_ty ~loc) in
     Value.return_term j

  | Syntax.Structure (s, xcs) ->
     Value.lookup_signature s >>= begin function
       | None -> Error.impossible ~loc "evaluating a structure of unknown signature %t"
                                  (Name.print_ident s)
       | Some lxts ->
          let rec fold ctx es xcs lxts =
            match xcs, lxts with
            | [], [] ->
               let es = List.rev es in
               let str = Tt.mk_structure ~loc s es in
               let t_str = Tt.mk_signature_ty ~loc s in
               let j_str = Jdg.mk_term ctx str t_str in
               Value.return_term j_str

            | (x, c) :: xcs, (lbl, _, t) :: lxts ->
                 let t_inst = Tt.instantiate_ty es t in
                 let jty = Jdg.mk_ty ctx t_inst in
                 check c jty >>= fun (ctx, e) ->
                 Value.add_bound x (Value.mk_term (Jdg.mk_term ctx e t_inst))
                 (fold ctx (e::es) xcs lxts)

            | _::_, [] -> Error.typing ~loc "this structure has too many fields"
            | [], _::_ -> Error.typing ~loc "this structure has too few fields"
          in
          fold Context.empty [] xcs lxts
     end

  | Syntax.Projection (c,p) ->
    infer c >>= as_term ~loc >>= fun (Jdg.Term (ctx,te,ty)) ->
    let jty = Jdg.mk_ty ctx ty in
    Equal.Monad.run (Equal.as_signature jty) >>= fun ((ctx,s),hyps) ->
    let te = Tt.mention_atoms hyps te in
    Value.lookup_signature s >>= begin function
      | None -> Error.impossible ~loc "projecting at unknown signature %t" (Name.print_ident s)
      | Some s_def ->
         let ty = Tt.field_type ~loc s s_def te p in
         let te = Tt.mk_projection ~loc te s p in
         let j = Jdg.mk_term ctx te ty in
         Value.return_term j
    end

  | Syntax.Yield c ->
    Value.lookup_continuation >>= begin function
      | Some k -> infer c >>= Value.apply_closure k
      | None -> Error.impossible ~loc "yield without continuation set"
      end

  | Syntax.Context ->
     Value.lookup_abstracting >>= fun lst ->
     let v = Value.from_list
               (List.map (fun jxt -> Value.mk_term jxt) lst) in
     Value.return v

  | Syntax.Congruence (c1,c2) ->
    infer c1 >>= as_term ~loc >>= fun (Jdg.Term (ctx,e1,t)) ->
    check c2 (Jdg.mk_ty ctx t) >>= fun (ctx,e2) ->
    Equal.Opt.run (Equal.congruence ~loc ctx e1 e2 t) >>= begin function
      | Some (ctx,hyps) ->
        let eq = Tt.mk_refl ~loc t e1 in
        let eq = Tt.mention_atoms hyps eq in
        let teq = Tt.mk_eq_ty ~loc t e1 e2 in
        let j = Jdg.mk_term ctx eq teq in
        let v = Value.mk_term j in
        Value.return (Value.from_option (Some v))
      | None -> Value.return (Value.from_option None)
      end

  | Syntax.String s ->
    Value.return (Value.mk_string s)

and require_equal ctx e1 e2 t =
  Equal.Opt.run (Equal.equal ctx e1 e2 t)

and require_equal_ty ~loc (Jdg.Ty (lctx, lte)) (Jdg.Ty (rctx, rte)) =
  Value.lookup_penv >>= fun penv ->
  let ctx = Context.join ~penv ~loc lctx rctx in
  Equal.Opt.run (Equal.equal_ty ctx lte rte)

and check ((c',loc) as c) (Jdg.Ty (ctx_check, t_check') as t_check) : (Context.t * Tt.term) Value.result =
  match c' with

  | Syntax.Type
  | Syntax.Bound _
  | Syntax.Function _
  | Syntax.Rec _
  | Syntax.Handler _
  | Syntax.External _
  | Syntax.Data _
  | Syntax.Nil
  | Syntax.Cons _
  | Syntax.Tuple _
  | Syntax.Where _
  | Syntax.With _
  | Syntax.Typeof _
  | Syntax.Match _
  | Syntax.Constant _
  | Syntax.Prod _
  | Syntax.Eq _
  | Syntax.Apply _
  | Syntax.Signature _
  | Syntax.Projection _
  | Syntax.Yield _
  | Syntax.Context
  | Syntax.Reduce _
  | Syntax.Congruence _
  | Syntax.Ref _
  | Syntax.Lookup _
  | Syntax.Update _
  | Syntax.Sequence _
  | Syntax.String _
  | Syntax.Structure _ ->
    (** this is the [check-infer] rule, which applies for all term formers "foo"
        that don't have a "check-foo" rule *)

    infer c >>= as_term ~loc >>= fun (Jdg.Term (ctxe, e, t')) ->
    require_equal_ty ~loc t_check (Jdg.mk_ty ctxe t') >>=
      begin function
        | Some (ctx, hyps) -> Value.return (ctx, Tt.mention_atoms hyps e)
        | None ->
           Value.print_term >>= fun pte ->
           Value.print_ty >>= fun pty ->
           Error.typing ~loc:(e.Tt.loc)
                        "the expression %t should have type@ %t@ but has type@ %t"
                        (pte e) (pty t_check') (pty t')
      end

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          Value.perform op vs >>= as_term ~loc >>= fun (Jdg.Term (ctxe, e', t')) ->
          require_equal_ty ~loc t_check (Jdg.mk_ty ctxe t') >>=
            begin function
              | Some (ctx, hyps) -> Value.return (ctx, Tt.mention_atoms hyps e')
              | None ->
                 Value.print_term >>= fun pte ->
                 Value.print_ty >>= fun pty ->
                 Error.typing ~loc:(e'.Tt.loc)
                              "the expression %t should have type@ %t@ but has type@ %t"
                              (pte e') (pty t_check') (pty t')
            end
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.Let (xcs, c) ->
     let_bind xcs (check c t_check)

  | Syntax.Assume ((x, t), c) ->
     check_ty t >>= fun t ->
     Value.add_abstracting ~loc x t (fun _ _ ->
     check c t_check)

  | Syntax.Ascribe (c1, c2) ->
     check_ty c2 >>= fun (Jdg.Ty (_,t') as t) ->
     require_equal_ty ~loc t_check t >>=
       begin function
         | Some (ctx, hyps) ->
            let jt = Jdg.mk_ty ctx t' in
            check c1 jt >>= fun (ctx,e) ->
            Value.return (ctx,Tt.mention_atoms hyps e)
         | None ->
            Value.print_ty >>= fun pty ->
            Error.typing ~loc:(snd c2)
                         "this type should be equal to@ %t"
                         (pty t_check')
       end

  | Syntax.Lambda (x,u,c) ->
    check_lambda ~loc t_check x u c

  | Syntax.Refl c ->
    Equal.Monad.run (Equal.as_eq t_check) >>= fun ((ctx, t', e1, e2),hyps) ->
    let t = Jdg.mk_ty ctx t' in
    check c t >>= fun (ctx, e) ->
    require_equal ctx e e1 t' >>=
     begin function
         | Some (ctx, hyps1) ->
            require_equal ctx e e2 t' >>=
              begin function
                | Some (ctx, hyps2) ->
                   let e = Tt.mk_refl ~loc t' e in
                   let e = Tt.mention_atoms hyps e in
                   let e = Tt.mention_atoms hyps1 e in
                   let e = Tt.mention_atoms hyps2 e in
                   Value.return (ctx, e)
                | None ->
                   Value.print_term >>= fun pte ->
                   Error.typing ~loc
                                "failed to check that the term@ %t is equal to@ %t"
                                (pte e) (pte e2)
              end
         | None ->
            Value.print_term >>= fun pte ->
            Error.typing ~loc
                         "failed to check that the term@ %t is equal to@ %t"
                         (pte e) (pte e1)
     end

and infer_lambda ~loc x u c =
  match u with
    | Some u ->
      check_ty u >>= fun (Jdg.Ty (ctxu, (Tt.Ty {Tt.loc=uloc;_} as u)) as ju) ->
      Value.add_abstracting ~loc:uloc x ju (fun _ y ->
      infer c >>= as_term ~loc:(snd c) >>= fun (Jdg.Term (ctxe,e,t)) ->
      Value.lookup_penv >>= fun penv ->
      let ctxe = Context.abstract ~penv ~loc ctxe y u in
      let ctx = Context.join ~penv ~loc ctxu ctxe in
      let e = Tt.abstract [y] e in
      let t = Tt.abstract_ty [y] t in
      let lam = Tt.mk_lambda ~loc x u e t
      and prod = Tt.mk_prod_ty ~loc x u t in
      Value.return_term (Jdg.mk_term ctx lam prod))
    | None ->
      Error.runtime ~loc "cannot infer the type of %t" (Name.print_ident x)

and infer_prod ~loc x u c =
  check_ty u >>= fun (Jdg.Ty (ctxu,u) as ju) ->
  let Tt.Ty {Tt.loc=uloc;_} = u in
  Value.add_abstracting ~loc:uloc x ju (fun _ y ->
  check_ty c >>= fun (Jdg.Ty (ctx,t)) ->
  Value.lookup_penv >>= fun penv ->
  let ctx = Context.abstract ~penv ~loc ctx y u in
  let ctx = Context.join ~penv ~loc ctx ctxu in
  let t = Tt.abstract_ty [y] t in
  let prod = Tt.mk_prod ~loc x u t in
  let typ = Tt.mk_type_ty ~loc in
  let j = Jdg.mk_term ctx prod typ in
  Value.return_term j)

and check_lambda ~loc t_check x u c : (Context.t * Tt.term) Value.result =
  Equal.Monad.run (Equal.as_prod t_check) >>= fun ((ctx,((_,a),b)),hypst) ->
  begin match u with
    | Some u ->
      check_ty u >>= fun (Jdg.Ty (_,u) as ju) ->
      require_equal_ty ~loc (Jdg.mk_ty ctx a) ju >>= begin function
        | Some (ctx,hypsu) ->
          Value.return (ctx,u,hypsu)
        | None ->
          Value.print_ty >>= fun pty ->
          Error.typing ~loc "this annotation has type %t but should have type %t"
            (pty u) (pty a)
      end
    | None ->
      Value.return (ctx,a,Name.AtomSet.empty)
  end >>= fun (ctx,u,hypsu) -> (* u a type equal to a under hypsu *)
  Value.add_abstracting ~loc x (Jdg.mk_ty ctx u) (fun ctx y ->
  let y' = Tt.mention_atoms hypsu (Tt.mk_atom ~loc y) in (* y' : a *)
  let b = Tt.instantiate_ty [y'] b in
  check c (Jdg.mk_ty ctx b) >>= fun (ctx,e) ->
  Value.lookup_penv >>= fun penv ->
  let ctx = Context.abstract ~penv ~loc ctx y u in
  let e = Tt.abstract [y] e in
  let b = Tt.abstract_ty [y] b in
  let lam = Tt.mk_lambda ~loc x u e b in
  (* lam : forall x : u, b
     == forall x : a, b by hypsu
     == check_ty by hypst *)
  let lam = Tt.mention_atoms (Name.AtomSet.union hypst hypsu) lam in
  Value.return (ctx,lam))

(** Suppose [e] has type [t], and [cs] is a list of computations [c1, ..., cn].
    Then [apply env e t cs] computes [xeus], [u] and [v] such that we can make
    a apply from [e], [xeus] and [u], and the type of the resulting expression
    is [v].
  *)
and apply ~loc (Jdg.Term (_, h, _) as jh) c =
  Equal.Monad.run (Equal.as_prod (Jdg.typeof jh)) >>= fun ((ctx,((x,a),b)),hyps) ->
  let h = Tt.mention_atoms hyps h in
  check c (Jdg.mk_ty ctx a) >>= fun (ctx,e) ->
  let res = Tt.mk_apply ~loc h x a b e in
  let out = Tt.instantiate_ty [e] b in
  let j = Jdg.mk_term ctx res out in
  Value.return_term j

and let_bind : 'a. _ -> 'a Value.result -> 'a Value.result = fun xcs cmp ->
  let rec fold vs = function
    | [] ->
      (* parallel let: only bind at the end *)
      let rec fold' = function
        | [] -> cmp
        | (x,v)::rem ->
          Value.add_bound x v (fold' rem)
      in
      fold' (List.rev vs)
    | (x,c) :: xcs ->
      infer c >>= fun v ->
      fold ((x,v)::vs) xcs
    in
  fold [] xcs

and match_cases ~loc cases v =
  let rec fold = function
    | [] ->
      Value.print_value >>= fun pval ->
      Error.runtime ~loc "no match found for %t" (pval v)
    | (xs, p, c) :: cases ->
      Matching.match_pattern p v >>= begin function
        | Some vs ->
          let rec fold2 xs vs = match xs, vs with
            | [], [] -> infer c
            | x::xs, v::vs ->
              Value.add_bound x v (fold2 xs vs)
            | _::_, [] | [], _::_ -> Error.impossible ~loc "bad multimatch case"
          in
          fold2 (List.rev xs) vs
        | None -> fold cases
      end
  in
  fold cases

and multimatch_cases ~loc op cases vs =
  let rec fold = function
    | [] ->
      Value.perform op vs
    | (xs, ps, c) :: cases ->
      Matching.multimatch_pattern ps vs >>= begin function
        | Some vs ->
          let rec fold2 xs vs = match xs, vs with
            | [], [] -> infer c
            | x::xs, v::vs ->
              Value.add_bound x v (fold2 xs vs)
            | _::_, [] | [], _::_ -> Error.impossible ~loc "bad multimatch case"
          in
          fold2 (List.rev xs) vs
        | None -> fold cases
      end
  in
  fold cases

and check_ty c : Jdg.ty Value.result =
  check c Jdg.ty_ty >>= fun (ctx, e) ->
  let t = Tt.ty e in
  let j = Jdg.mk_ty ctx t in
  Value.return j

let comp_value ((_, loc) as c) =
  let r = infer c in
  Value.top_handle ~loc r

let comp_handle (xs,c) =
  Value.mk_closure' (fun vs ->
      let rec fold2 xs vs = match xs,vs with
        | [], [] -> infer c
        | x::xs, v::vs -> Value.add_bound x v (fold2 xs vs)
        | [],_::_ | _::_,[] -> Error.impossible ~loc:(snd c) "bad top handler case"
      in
      fold2 xs vs)

let comp_signature ~loc lxcs =
  let rec fold ys yts lxts = function

    | [] ->
       let lxts = List.rev lxts in
       Value.return lxts

    | (l,x,c) :: lxcs ->
       check_ty c >>= fun (Jdg.Ty (ctxt,t)) ->
       if not (Context.is_subset ctxt yts)
       then Error.runtime ~loc "signature field %t has unresolved assumptions"
                          (Name.print_ident l)
       else begin
         let jt = Jdg.mk_ty ctxt t
         and tabs = Tt.abstract_ty ys t in
         Value.add_abstracting ~loc x jt (fun _ y ->
           fold (y::ys) ((y,t)::yts) ((l,x,tabs) :: lxts) lxcs)
       end
  in
  Value.top_handle ~loc (fold [] [] [] lxcs)


(** Evaluation of toplevel computations *)

let parse lex parse resource =
  try
    lex parse resource
  with
  | Ulexbuf.Parse_Error (w, p_start, p_end) ->
     let loc = Location.make p_start p_end in
     Error.syntax ~loc "Unexpected: %s" w


(** The help text printed when [#help] is used. *)
let help_text = "Toplevel directives:
#environment. .... print current environment
#help. ........... print this help
#quit. ........... exit

Parameter <ident> ... <ident> : <type> .     assume variable <ident> has type <type>
Let <ident> := <expr> .                      define <ident> to be <expr>
Check <expr> .                               check the type of <expr>

The syntax is vaguely Coq-like. The strict equality is written with a double ==.
" ;;


let (>>=) = Value.top_bind
let (>>) m1 m2 = m1 >>= fun () -> m2
let return = Value.top_return

let rec fold f acc = function
  | [] -> return acc
  | x::rem -> f acc x >>= fun acc ->
    fold f acc rem

let rec exec_cmd base_dir interactive c =
  Value.top_get_env >>= fun env ->
  Value.top_bound_names >>= fun xs ->
  let (c', loc) = Desugar.toplevel env xs c in
  match c' with

  | Syntax.DeclOperation (x, k) ->
     Value.add_operation ~loc x k >>= fun () ->
     if interactive then Format.printf "Operation %t is declared.@." (Name.print_ident x) ;
     return ()

  | Syntax.DeclData (x, k) ->
     Value.add_data ~loc x k >>= fun () ->
     if interactive then Format.printf "Data constructor %t is declared.@." (Name.print_ident x) ;
     return ()

  | Syntax.DeclConstant (x, c) ->
     Value.top_handle ~loc:(snd c) (check_ty c) >>= fun (Jdg.Ty (ctxt, t)) ->
      if Context.is_empty ctxt
      then
        Value.add_constant ~loc x t >>= fun () ->
        (if interactive then Format.printf "Constant %t is declared.@." (Name.print_ident x) ;
         return ())
      else
        Error.typing "Constants may not depend on free variables" ~loc:(snd c)

  | Syntax.DeclSignature (s, lxcs) ->
     begin
       match Value.find_signature env (List.map (fun (l,_,_) -> l) lxcs) with
       | Some s -> Error.syntax ~loc "signature %t already has these fields"
                                  (Name.print_ident s)
       | None ->
          comp_signature ~loc lxcs >>= fun lxts ->
          Value.add_signature ~loc s lxts  >>= fun () ->
          (if interactive then Format.printf "Signature %t is declared.@." (Name.print_ident s) ;
           return ())
     end

  | Syntax.TopHandle lst ->
    fold (fun () (op, xc) ->
        comp_handle xc >>= fun f ->
        Value.add_handle op f) () lst

  | Syntax.TopLet (x, c) ->
     comp_value c >>= fun v ->
     Value.add_topbound ~loc x v >>= fun () ->
     if interactive && not (Name.is_anonymous x)
      then Format.printf "%t is defined.@." (Name.print_ident x) ;
     return ()

  | Syntax.TopDo c ->
     comp_value c >>= fun v ->
     Value.top_print_value >>= fun print_value ->
     (if interactive then Format.printf "%t@." (print_value v) ;
     return ())

  | Syntax.TopFail c ->
     Value.catch (comp_value c) >>= begin function
     | Error.Err err ->
        (if interactive then Format.printf "The command failed with error:\n%t@." (Error.print err));
        return ()
     | Error.OK v ->
        Value.top_print_value >>= fun pval ->
        Error.runtime ~loc "The command has not failed: got %t." (pval v)
     end

  | Syntax.Include (fs,once) ->
    fold (fun () f ->
         (* don't print deeper includes *)
         if interactive then Format.printf "#including %s@." f ;
           let f =
             if Filename.is_relative f
             then Filename.concat base_dir f
             else f
           in
           use_file (f, None, false, once) >>
           (if interactive then Format.printf "#processed %s@." f ;
           return ())) () fs

  | Syntax.Verbosity i -> Config.verbosity := i; return ()

  | Syntax.Environment ->
    Value.print_env >>= fun p ->
    Format.printf "%t@." p;
    return ()

  | Syntax.Help ->
    Format.printf "%s@." help_text ; return ()

  | Syntax.Quit ->
    exit 0

and use_file (filename, line_limit, interactive, once) =
  (if once then Value.included filename else return false) >>= fun skip ->
  if skip then return () else
    begin
      let cmds = parse (Lexer.read_file ?line_limit) Parser.file filename in
      let base_dir = Filename.dirname filename in
      Value.push_file filename >>
      fold (fun () c -> exec_cmd base_dir interactive c) () cmds
    end

