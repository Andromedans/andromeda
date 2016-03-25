(** Evaluation of computations *)

(** Notation for the monadic bind *)
let (>>=) = Runtime.bind

(** A filter that verifies the result is a term. *)
let as_term ~loc v =
  let e = Runtime.as_term ~loc v in
    Runtime.return e

(** Returns the atom with its natural type in [ctx] *)
let as_atom ~loc v =
  as_term ~loc v >>= fun j ->
  match Jdg.shape ~loc j with
    | Jdg.Atom x -> Runtime.return x
    | _ -> Runtime.(error ~loc (ExpectedAtom j))
      

let as_handler ~loc v =
  let e = Runtime.as_handler ~loc v in
  Runtime.return e

let as_ref ~loc v =
  let e = Runtime.as_ref ~loc v in
  Runtime.return e

(** Form a judgement *)
let jdg_form ~loc s =
  Runtime.lookup_typing_env >>= fun env ->
  Runtime.return (Jdg.form ~loc env s)

(** Evaluate a computation -- infer mode. *)
let rec infer {Location.thing=c'; loc} =
  match c' with
    | Syntax.Bound i ->
       Runtime.lookup_bound ~loc i

    | Syntax.Type ->
      jdg_form ~loc Jdg.Type >>=
      Runtime.return_term

    | Syntax.Function (x, c) ->
       let f v =
         Runtime.add_bound x v
           (infer c)
       in
       Runtime.return_closure f

    | Syntax.Constructor (t, cs) ->
       let rec fold vs = function
         | [] ->
            let vs = List.rev vs in
            let v = Runtime.mk_tag t vs in
            Runtime.return v
         | c :: cs ->
            infer c >>= fun v ->
            fold (v :: vs) cs
       in
       fold [] cs

    | Syntax.Tuple cs ->
      let rec fold vs = function
        | [] -> Runtime.return (Runtime.mk_tuple (List.rev vs))
        | c :: cs -> (infer c >>= fun v -> fold (v :: vs) cs)
      in
      fold [] cs

    | Syntax.Handler {Syntax.handler_val; handler_ops; handler_finally} ->
        let handler_val =
          begin match handler_val with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~loc handler_val infer v
            in
            Some f
          end
        and handler_ops = Name.IdentMap.mapi (fun op cases ->
            let f {Runtime.args=vs;checking} =
              match_op_cases ~loc op cases vs checking
            in
            f)
          handler_ops
        and handler_finally =
          begin match handler_finally with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~loc handler_finally infer v
            in
            Some f
          end
        in
        Runtime.return_handler handler_val handler_ops handler_finally

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op vs
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.With (c1, c2) ->
     infer c1 >>= as_handler ~loc >>= fun h ->
     Runtime.handle_comp h (infer c2)

  | Syntax.Let (xcs, c) ->
     let_bind xcs (infer c)

  | Syntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (infer c)

  | Syntax.Now (x,c1,c2) ->
    infer c1 >>= fun v ->
    Runtime.now ~loc x v (infer c2)

  | Syntax.Ref c ->
     infer c >>= fun v ->
     Runtime.mk_ref v

  | Syntax.Lookup c ->
     infer c >>= as_ref ~loc >>= fun x ->
     Runtime.lookup_ref x

  | Syntax.Update (c1, c2) ->
     infer c1 >>= as_ref ~loc >>= fun x ->
     infer c2 >>= fun v ->
     Runtime.update_ref x v >>= fun () ->
     Runtime.return_unit

  | Syntax.Sequence (c1, c2) ->
     infer c1 >>= fun v ->
     sequence ~loc v >>= fun () ->
     infer c2

  | Syntax.Assume ((x, t), c) ->
     check_ty t >>= fun t ->
     Runtime.add_free ~loc x t (fun _ ->
       infer c)

  | Syntax.Where (c1, c2, c3) ->
    infer c2 >>= as_atom ~loc >>= fun (Jdg.JAtom (_, a, _)) ->
    infer c1 >>= fun v1 -> as_term ~loc v1 >>= fun (Jdg.Term (ctx, e1, t1)) ->
    begin match Jdg.Ctx.lookup_atom a ctx with
    | None -> infer c3 >>=
       as_term ~loc:(c3.Location.loc) >>= fun _ ->
       Runtime.return v1
    | Some ja ->
       let Jdg.Ty (_, ta) as jta = Jdg.atom_ty ja in
       check c3 jta >>= fun (Jdg.Term (ctx, e2, _)) ->
       let ctx_s = Jdg.Ctx.substitute ~loc a (ctx,e2,ta) in
       let te_s = Tt.substitute [a] [e2] e1 in
       let ty_s = Tt.substitute_ty [a] [e2] t1 in
       let j_s = Jdg.mk_term ctx_s te_s ty_s in
       Runtime.return_term j_s
    end

  | Syntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases infer

  | Syntax.External s ->
     begin match External.lookup s with
       | None -> Runtime.(error ~loc (UnknownExternal s))
       | Some v -> v loc
     end

  | Syntax.Ascribe (c1, c2) ->
     check_ty c2 >>= fun (Jdg.Ty (_,t') as t) ->
     check c1 t >>=
     Runtime.return_term

  | Syntax.Constant x ->
    jdg_form ~loc (Jdg.Constant x) >>=
    Runtime.return_term

  | Syntax.Lambda (x, None, _) ->
    Runtime.(error ~loc (UnannotatedLambda x))

  | Syntax.Lambda (x, Some u, c) ->
    check_ty u >>= fun ju ->
    Runtime.add_abstracting ~loc:(u.Location.loc) x ju (fun jy ->
    infer c >>= as_term ~loc:(c.Location.loc) >>= fun je ->
    jdg_form ~loc (Jdg.Lambda (jy, je)) >>=
    Runtime.return_term)

  | Syntax.Apply (c1, c2) ->
    infer c1 >>= begin function
      | Runtime.Term j ->
        apply ~loc j c2
      | Runtime.Closure f ->
        infer c2 >>= fun v ->
        Runtime.apply_closure f v
      | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
        Runtime.Ref _ | Runtime.String _ | Runtime.Ident _ as h ->
        Runtime.(error ~loc (Inapplicable h))
    end

  | Syntax.Prod (x,u,c) ->
    check_ty u >>= fun ju ->
    Runtime.add_abstracting ~loc:u.Location.loc x ju (fun jy ->
    check_ty c >>= fun jt ->
    jdg_form ~loc (Jdg.Prod (jy, jt)) >>=
    Runtime.return_term)

  | Syntax.Eq (c1, c2) ->
     infer c1 >>= as_term ~loc:c1.Location.loc >>= fun j1 ->
     let (Jdg.Ty (_,t1')) as t1 = Jdg.typeof j1 in
     check c2 t1 >>= fun j2 ->
     jdg_form ~loc (Jdg.Eq (j1,j2)) >>=
     Runtime.return_term

  | Syntax.Refl c ->
     infer c >>= as_term ~loc:c.Location.loc >>= fun j ->
     jdg_form ~loc (Jdg.Refl j) >>=
     Runtime.return_term

  | Syntax.Yield c ->
    infer c >>= fun v ->
    Runtime.continue ~loc v

  | Syntax.Hypotheses ->
     Runtime.lookup_abstracting >>= fun lst ->
     let v = Predefined.mk_list lst in
     Runtime.return v

  | Syntax.Congruence (c1,c2) ->
    infer c1 >>= as_term ~loc >>= fun (Jdg.Term (ctx,e1,t) as j1) ->
    check c2 (Jdg.typeof j1) >>= fun (Jdg.Term (ctx, e2, _)) ->
    Equal.congruence ~loc ctx e1 e2 t >>= begin function
      | Some (ctx,hyps) ->
        let eq = Tt.mk_refl ~loc t e1 in
        let eq = Tt.mention_atoms hyps eq in
        let teq = Tt.mk_eq_ty ~loc t e1 e2 in
        let j = Jdg.mk_term ctx eq teq in
        let v = Runtime.mk_term j in
        Runtime.return (Predefined.from_option (Some v))
      | None -> Runtime.return (Predefined.from_option None)
      end

  | Syntax.Extensionality (c1,c2) ->
    infer c1 >>= as_term ~loc >>= fun (Jdg.Term (ctx,e1,t) as j1) ->
    check c2 (Jdg.typeof j1) >>= fun (Jdg.Term (ctx, e2, _)) ->
    Equal.extensionality ~loc ctx e1 e2 t >>= begin function
      | Some (ctx,hyps) ->
        let eq = Tt.mk_refl ~loc t e1 in
        let eq = Tt.mention_atoms hyps eq in
        let teq = Tt.mk_eq_ty ~loc t e1 e2 in
        let j = Jdg.mk_term ctx eq teq in
        let v = Runtime.mk_term j in
        Runtime.return (Predefined.from_option (Some v))
      | None -> Runtime.return (Predefined.from_option None)
      end

  | Syntax.Reduction c ->
     infer c >>= as_term ~loc >>= fun (Jdg.Term (ctx, e, t)) ->
     Equal.reduction_step ctx e >>=
       begin function
         | Some ((ctx, e'), hyps) ->
            let eq = Tt.mk_refl ~loc t e in
            let eq = Tt.mention_atoms hyps eq in
            let teq = Tt.mk_eq_ty ~loc t e e' in
            let eqj = Jdg.mk_term ctx eq teq in
            Runtime.return (Predefined.from_option (Some (Runtime.mk_term eqj)))
         | None -> Runtime.return (Predefined.from_option None)
       end

  | Syntax.String s ->
    Runtime.return (Runtime.mk_string s)

  | Syntax.Occurs (c1,c2) ->
    infer c1 >>= as_atom ~loc >>= fun (Jdg.JAtom (_,x,_)) ->
    infer c2 >>= as_term ~loc >>= fun (Jdg.Term (ctx,_,_)) ->
    begin match Jdg.Ctx.lookup_atom x ctx with
      | Some jx ->
        let j = Jdg.term_of_ty (Jdg.atom_ty jx) in
        Runtime.return (Predefined.from_option (Some (Runtime.mk_term j)))
      | None ->
        Runtime.return (Predefined.from_option None)
    end

  | Syntax.Context c ->
    infer c >>= as_term ~loc >>= fun (Jdg.Term (ctx,_,_)) ->
    let xts = Jdg.Ctx.elements ctx in
    let js = List.map (fun j -> Runtime.mk_term (Jdg.atom_term ~loc j)) xts in
    Runtime.return (Predefined.mk_list js)

  | Syntax.Ident x ->
    Runtime.return (Runtime.mk_ident x)

and require_equal_ty ~loc (Jdg.Ty (lctx, lte)) (Jdg.Ty (rctx, rte)) =
  let ctx = Jdg.Ctx.join ~loc lctx rctx in
  Equal.equal_ty ctx lte rte

and check_default ~loc v (Jdg.Ty (_, t_check') as t_check) =
  as_term ~loc v >>= fun (Jdg.Term (_, e, _) as je) ->
  let jt = Jdg.typeof je in
  require_equal_ty ~loc t_check jt >>=
    begin function
      | Some (ctx, hyps) ->
        let e = Tt.mention_atoms hyps e in
        Runtime.return (Jdg.mk_term ctx e t_check')
      | None ->
         Runtime.(error ~loc (TypeMismatch (jt, t_check)))
    end

and check ({Location.thing=c';loc} as c) (Jdg.Ty (_, t_check') as t_check) =
  match c' with
  | Syntax.Type
  | Syntax.Bound _
  | Syntax.Function _
  | Syntax.Handler _
  | Syntax.External _
  | Syntax.Constructor _
  | Syntax.Tuple _
  | Syntax.Where _
  | Syntax.With _
  | Syntax.Constant _
  | Syntax.Prod _
  | Syntax.Eq _
  | Syntax.Apply _
  | Syntax.Yield _
  | Syntax.Hypotheses
  | Syntax.Congruence _
  | Syntax.Extensionality _
  | Syntax.Reduction _
  | Syntax.Ref _
  | Syntax.Lookup _
  | Syntax.Update _
  | Syntax.String _
  | Syntax.Occurs _
  | Syntax.Context _
  | Syntax.Ident _ ->
    (** this is the [check-infer] rule, which applies for all term formers "foo"
        that don't have a "check-foo" rule *)

    infer c >>= fun v ->
    check_default ~loc v t_check

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op ~checking:t_check vs >>= fun v ->
          check_default ~loc v t_check
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.Let (xcs, c) ->
     let_bind xcs (check c t_check)

  | Syntax.Sequence (c1,c2) ->
    infer c1 >>= fun v ->
    sequence ~loc v >>= fun () ->
    check c2 t_check

  | Syntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (check c t_check)

  | Syntax.Now (x,c1,c2) ->
    infer c1 >>= fun v ->
    Runtime.now ~loc x v (check c2 t_check)

  | Syntax.Assume ((x, t), c) ->
     check_ty t >>= fun t ->
     Runtime.add_free ~loc x t (fun _ ->
     check c t_check)

  | Syntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases (fun c -> check c t_check)

  | Syntax.Ascribe (c1, c2) ->
     check_ty c2 >>= fun (Jdg.Ty (_,t') as t) ->
     require_equal_ty ~loc t_check t >>=
       begin function
         | Some (ctx, hyps) ->
            let jt = Jdg.mk_ty ctx t' in
            check c1 jt >>= fun (Jdg.Term (ctx, e, _)) ->
            let e = Tt.mention_atoms hyps e in
            let Jdg.Ty (_, t_check') = t_check in
            Runtime.return (Jdg.mk_term ctx e t_check')
         | None ->
            Runtime.(error ~loc:(c2.Location.loc) (TypeMismatch (t, t_check)))
       end

  | Syntax.Lambda (x,u,c) ->
    check_lambda ~loc t_check x u c

  | Syntax.Refl c ->
    Equal.as_eq t_check >>= fun ((ctx, t', e1, e2),hyps) ->
    let t = Jdg.mk_ty ctx t' in
    check c t >>= fun (Jdg.Term (ctx, e, _)) ->
    Equal.equal ctx e e1 t' >>= begin function
      | None ->
        Runtime.(error ~loc (EqualityFail (e, e1)))
      | Some (ctx, hyps1) ->
        Equal.equal ctx e e2 t' >>=
          begin function
            | None ->
              Runtime.(error ~loc (EqualityFail (e, e2)))
            | Some (ctx, hyps2) ->
              let e = Tt.mk_refl ~loc t' e in
              let e = Tt.mention_atoms hyps e in
              let e = Tt.mention_atoms hyps1 e in
              let e = Tt.mention_atoms hyps2 e in
              let Jdg.Ty (_, t_check') = t_check in
              Runtime.return (Jdg.mk_term ctx e t_check')
          end
      end

and check_lambda ~loc t_check x u c =
  Equal.as_prod t_check >>= fun ((ctx,((_,a),b)),hypst) ->
  begin match u with
    | Some u ->
      check_ty u >>= fun (Jdg.Ty (_,u) as ju) ->
      require_equal_ty ~loc (Jdg.mk_ty ctx a) ju >>= begin function
        | Some (ctx,hypsu) ->
          Runtime.return (ctx,u,hypsu)
        | None ->
          Runtime.lookup_penv >>= fun penv ->
          Runtime.(error ~loc (TypeMismatch (ju, Jdg.mk_ty ctx a)))
      end
    | None ->
      Runtime.return (ctx,a,Name.AtomSet.empty)
  end >>= fun (ctx,u,hypsu) -> (* [u] a type equal to [a] under [hypsu] *)
  Runtime.add_abstracting ~loc x (Jdg.mk_ty ctx u) (fun (Jdg.JAtom (ctx, y, _)) ->
  let y' = Tt.mention_atoms hypsu (Tt.mk_atom ~loc y) in (* y' : a *)
  let b = Tt.instantiate_ty [y'] b in
  check c (Jdg.mk_ty ctx b) >>= fun (Jdg.Term (ctx, e, _)) ->
  let ctx = Jdg.Ctx.abstract ~loc ctx y u in
  let e = Tt.abstract [y] e in
  let b = Tt.abstract_ty [y] b in
  let lam = Tt.mk_lambda ~loc x u e b in
  (* lam : forall x : u, b
     == forall x : a, b by hypsu
     == check_ty by hypst *)
  let lam = Tt.mention_atoms (Name.AtomSet.union hypst hypsu) lam in
  let Jdg.Ty (_, t_check') = t_check in
  Runtime.return (Jdg.mk_term ctx lam t_check'))

and apply ~loc (Jdg.Term (_, h, _) as jh) c =
  Equal.as_prod (Jdg.typeof jh) >>= fun ((ctx,((x,a),b)),hyps) ->
  let h = Tt.mention_atoms hyps h in
  check c (Jdg.mk_ty ctx a) >>= fun (Jdg.Term (ctx, e, _)) ->
  let res = Tt.mk_apply ~loc h x a b e in
  let out = Tt.instantiate_ty [e] b in
  let j = Jdg.mk_term ctx res out in
  Runtime.return_term j

and sequence ~loc v =
  match v with
    | Runtime.Tuple [] -> Runtime.return ()
    | _ ->
      Runtime.lookup_penv >>= fun penv ->
      Print.warning "%t: Sequence:@ The value %t should be ()" (Location.print loc) (Runtime.print_value ~penv v);
      Runtime.return ()

and let_bind : 'a. _ -> 'a Runtime.comp -> 'a Runtime.comp = fun xcs cmd ->
  let rec fold xvs = function
    | [] ->
      (* parallel let: only bind at the end *)
      List.fold_left  (fun cmd (x,v) -> Runtime.add_bound x v cmd) cmd xvs
    | (x, c) :: xcs ->
      infer c >>= fun v ->
      fold ((x, v) :: xvs) xcs
    in
  fold [] xcs

and letrec_bind : 'a. _ -> 'a Runtime.comp -> 'a Runtime.comp = fun fxcs ->
  let gs =
    List.map
      (fun (f, x, c) -> (f, (fun v -> Runtime.add_bound x v (infer c))))
      fxcs
  in
  Runtime.add_bound_rec gs

(* [match_cases loc cases eval v] tries for each case in [cases] to match [v]
   and if successful continues on the computation using [eval] with the pattern variables bound. *)
and match_cases : type a. loc:_ -> _ -> (Syntax.comp -> a Runtime.comp) -> _ -> a Runtime.comp
 = fun ~loc cases eval v ->
  let rec fold = function
    | [] ->
      Runtime.lookup_penv >>= fun penv ->
      Runtime.(error ~loc (MatchFail v))
    | (xs, p, c) :: cases ->
      Matching.match_pattern p v >>= begin function
        | Some vs ->
          let rec fold2 xs vs = match xs, vs with
            | [], [] -> eval c
            | x::xs, v::vs ->
              Runtime.add_bound x v (fold2 xs vs)
            | _::_, [] | [], _::_ -> assert false
          in
          fold2 (List.rev xs) vs
        | None -> fold cases
      end
  in
  fold cases

and match_op_cases ~loc op cases vs checking =
  let rec fold = function
    | [] ->
      Runtime.operation op ?checking vs >>= fun v ->
      Runtime.continue ~loc v
    | (xs, ps, pt, c) :: cases ->
      Matching.match_op_pattern ps pt vs checking >>= begin function
        | Some vs ->
          let rec fold2 xs vs = match xs, vs with
            | [], [] -> infer c
            | x::xs, v::vs ->
              Runtime.add_bound x v (fold2 xs vs)
            | _::_, [] | [], _::_ -> assert false
          in
          fold2 (List.rev xs) vs
        | None -> fold cases
      end
  in
  fold cases

and check_ty c : Jdg.ty Runtime.comp =
  check c Jdg.ty_ty >>= fun j ->
  Runtime.return (Jdg.is_ty ~loc:c.Location.loc j)


(** Move to toplevel monad *)

let comp_value c =
  let r = infer c in
  Runtime.top_handle ~loc:c.Location.loc r

let comp_handle (xs,y,c) =
  Runtime.top_return_closure (fun (vs,checking) ->
      let rec fold2 xs vs = match xs,vs with
        | [], [] ->
           begin match y with
           | Some y ->
              let checking = match checking with
                | Some jt -> Some (Runtime.mk_term (Jdg.term_of_ty jt))
                | None -> None
              in
              let vy = Predefined.from_option checking in
              Runtime.add_bound y vy (infer c)
           | None -> infer c
           end
        | x::xs, v::vs -> Runtime.add_bound x v (fold2 xs vs)
        | [],_::_ | _::_,[] -> assert false
      in
      fold2 xs vs)

(** Toplevel commands *)

let (>>=) = Runtime.top_bind
let return = Runtime.top_return

let rec mfold f acc = function
  | [] -> return acc
  | x::rem -> f acc x >>= fun acc ->
     mfold f acc rem

let toplet_bind ~loc ~quiet xcs =
  let rec fold xvs = function
    | [] ->
       (* parallel let: only bind at the end *)
       List.fold_left
         (fun cmd (x,v) ->
            Runtime.add_topbound ~loc x v >>= fun () ->
            if not quiet && not (Name.is_anonymous x)
            then Format.printf "%t is defined.@." (Name.print_ident x) ;
            cmd)
         (return ())
         xvs
    | (x, c) :: xcs ->
       comp_value c >>= fun v ->
       fold ((x, v) :: xvs) xcs
  in
  fold [] xcs

let topletrec_bind ~loc ~quiet fxcs =
  let gs =
    List.map
      (fun (f, x, c) -> (f, (fun v -> Runtime.add_bound x v (infer c))))
      fxcs
  in
  Runtime.add_topbound_rec ~loc gs >>= fun () ->
  if not quiet then
    List.iter (fun (f, _, _) ->
        if not (Name.is_anonymous f) then
          Format.printf "%t is defined.@." (Name.print_ident f)) fxcs ;
  return ()

let add_def = function
  | Syntax.ML_Alias _ -> return ()
  | Syntax.ML_Sum lst ->
    mfold (fun () (cstr, _) -> Runtime.add_forbidden cstr) () lst

let rec toplevel ~quiet {Location.thing=c;loc} =
  match c with

  | Syntax.DefMLType lst ->
    mfold (fun names (t,(_,def)) -> add_def def >>= fun () -> return (t::names)) [] lst >>= fun names ->
    let names = List.rev names in
    (if not quiet then Format.printf "ML type%s %t declared.@." (match names with [_] -> "" | _ -> "s") (Print.sequence Name.print_ident " " names));
    return ()

  | Syntax.DefMLTypeRec lst ->
    mfold (fun names (t,(_,def)) -> add_def def >>= fun () -> return (t::names)) [] lst >>= fun names ->
    let names = List.rev names in
    (if not quiet then Format.printf "ML type%s %t declared.@." (match names with [_] -> "" | _ -> "s") (Print.sequence Name.print_ident " " names));
    return ()

  | Syntax.DeclOperation (x, k) ->
     Runtime.add_forbidden x >>= fun () ->
     if not quiet then Format.printf "Operation %t is declared.@." (Name.print_ident x) ;
     return ()

  | Syntax.DeclConstants (xs, c) ->
     Runtime.top_handle ~loc:(c.Location.loc) (check_ty c) >>= fun (Jdg.Ty (ctxt, t)) ->
     if Jdg.Ctx.is_empty ctxt
     then
       let rec fold = function
         | [] -> return ()
         | x :: xs ->
            Runtime.add_constant ~loc x t >>= fun () ->
            (if not quiet then Format.printf "Constant %t is declared.@." (Name.print_ident x) ;
             fold xs)
       in
       fold xs
     else
       Runtime.(error ~loc ConstantDependency)

  | Syntax.TopHandle lst ->
     mfold (fun () (op, xc) ->
         comp_handle xc >>= fun f ->
         Runtime.add_handle op f) () lst

  | Syntax.TopLet xcs ->
     toplet_bind ~loc ~quiet xcs

  | Syntax.TopLetRec fxcs ->
     topletrec_bind ~loc ~quiet fxcs

  | Syntax.TopDynamic (x,c) ->
     comp_value c >>= fun v ->
     Runtime.add_dynamic ~loc x v

  | Syntax.TopNow (x,c) ->
     comp_value c >>= fun v ->
     Runtime.top_now ~loc x v

  | Syntax.TopDo c ->
     comp_value c >>= fun v ->
     Runtime.top_lookup_penv >>= fun penv ->
     (if not quiet then Format.printf "%t@." (Runtime.print_value ~penv v) ;
      return ())

  | Syntax.TopFail c ->
     Runtime.catch (fun () -> comp_value (Lazy.force c)) >>= begin function

     | Runtime.Caught exn  ->
        begin
          Runtime.top_lookup_penv >>= fun penv ->
          match exn with
          | Runtime.Error {Location.thing=err; loc} ->
             (if not quiet then Format.printf "The command failed with error:@\n%t:@ %t@."
                                              (Location.print loc)
                                              (Runtime.print_error ~penv err)
             );
             return ()
          | _ -> raise exn
        end

     | Runtime.Value v ->
        Runtime.top_lookup_penv >>= fun penv ->
        Runtime.(error ~loc (FailureFail v))
     end

  | Syntax.Included lst ->
    mfold (fun () (fn, cmds) ->
        (if not quiet then Format.printf "#including %s@." fn);
        mfold (fun () cmd -> toplevel ~quiet:true cmd) () cmds >>= fun () ->
        (if not quiet then Format.printf "#processed %s@." fn);
        return ())
      () lst

  | Syntax.Verbosity i -> Config.verbosity := i; return ()

  | Syntax.Quit ->
     exit 0

