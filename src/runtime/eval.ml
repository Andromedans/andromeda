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
  match Jdg.shape j with
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
  Runtime.lookup_typing_signature >>= fun signature ->
  Runtime.return (Jdg.form ~loc signature s)

(** Evaluate a computation -- infer mode. *)
let rec infer {Location.thing=c'; loc} =
  match c' with
    | Syntax.Bound i ->
       Runtime.lookup_bound ~loc i

    | Syntax.Type ->
      jdg_form ~loc Jdg.Type >>=
      Runtime.return_term

    | Syntax.Function (_, c) ->
       let f v =
         Runtime.add_bound v
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
    infer c2 >>= as_atom ~loc >>= fun a ->
    infer c1 >>= as_term ~loc:(c1.Location.loc) >>= fun je ->
    begin match Jdg.occurs a je with
    | None ->
       check c3 (Jdg.atom_ty a) >>= fun _ ->
       Runtime.return_term je
    | Some a ->
       check c3 (Jdg.atom_ty a) >>= fun js ->
       let j = Jdg.substitute ~loc je a js in
       Runtime.return_term j
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
     check_ty c2 >>= fun t ->
     check c1 t >>=
     Runtime.return_term

  | Syntax.Constant x ->
    jdg_form ~loc (Jdg.Constant x) >>=
    Runtime.return_term

  | Syntax.Lambda (x, None, _) ->
    Runtime.(error ~loc (UnannotatedLambda x))

  | Syntax.Lambda (x, Some u, c) ->
    check_ty u >>= fun ju ->
    Runtime.add_free ~loc:(u.Location.loc) x ju (fun jy ->
    let vy = Jdg.atom_term ~loc:(u.Location.loc) jy in
    Predefined.add_abstracting vy
    (infer c >>= as_term ~loc:(c.Location.loc) >>= fun je ->
    jdg_form ~loc (Jdg.Lambda (jy, je)) >>=
    Runtime.return_term))

  | Syntax.Apply (c1, c2) ->
    infer c1 >>= begin function
      | Runtime.Term j ->
        apply ~loc j c2
      | Runtime.Closure f ->
        infer c2 >>= fun v ->
        Runtime.apply_closure f v
      | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
        Runtime.Ref _ | Runtime.String _ as h ->
        Runtime.(error ~loc (Inapplicable h))
    end

  | Syntax.Prod (x,u,c) ->
    check_ty u >>= fun ju ->
    Runtime.add_free ~loc:u.Location.loc x ju (fun jy ->
    let vy = Jdg.atom_term ~loc:(u.Location.loc) jy in
    Predefined.add_abstracting vy
    (check_ty c >>= fun jt ->
    jdg_form ~loc (Jdg.Prod (jy, jt)) >>=
    Runtime.return_term))

  | Syntax.Eq (c1, c2) ->
     infer c1 >>= as_term ~loc:c1.Location.loc >>= fun j1 ->
     let t1 = Jdg.typeof j1 in
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

  | Syntax.CongrProd (c1, c2, c3) ->
    infer c1 >>= as_atom ~loc:c1.Location.loc >>= fun x ->
    infer c2 >>= as_term ~loc:c2.Location.loc >>= fun ja ->
    infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jb ->
    let eqa = Jdg.reflect_ty_eq ~loc:c2.Location.loc ja
    and eqb = Jdg.reflect_ty_eq ~loc:c3.Location.loc jb in
    let eq = Jdg.congr_prod_ty ~loc eqa x x eqb in
    let e = Jdg.refl_of_eq_ty ~loc eq in
    Runtime.return_term e

  | Syntax.CongrApply (c1, c2, c3, c4, c5) ->
    infer c1 >>= as_atom ~loc:c1.Location.loc >>= fun x ->
    infer c2 >>= as_term ~loc:c2.Location.loc >>= fun jh ->
    infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jarg ->
    infer c4 >>= as_term ~loc:c4.Location.loc >>= fun ja ->
    infer c5 >>= as_term ~loc:c5.Location.loc >>= fun jb ->
    let eqh = Jdg.reflect ~loc:c2.Location.loc jh
    and eqarg = Jdg.reflect ~loc:c3.Location.loc jarg
    and eqa = Jdg.reflect_ty_eq ~loc:c4.Location.loc ja
    and eqb = Jdg.reflect_ty_eq ~loc:c5.Location.loc jb in
    let eq = Jdg.congr_apply ~loc eqa x x eqb eqh eqarg in
    let e = Jdg.refl_of_eq ~loc eq in
    Runtime.return_term e

  | Syntax.CongrLambda (c1, c2, c3, c4) ->
    infer c1 >>= as_atom ~loc:c1.Location.loc >>= fun x ->
    infer c2 >>= as_term ~loc:c2.Location.loc >>= fun ja ->
    infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jb ->
    infer c4 >>= as_term ~loc:c4.Location.loc >>= fun jbody ->
    let eqbody = Jdg.reflect ~loc:c4.Location.loc jbody
    and eqa = Jdg.reflect_ty_eq ~loc:c2.Location.loc ja
    and eqb = Jdg.reflect_ty_eq ~loc:c3.Location.loc jb in
    let eq = Jdg.congr_lambda ~loc eqa x x eqb eqbody in
    let e = Jdg.refl_of_eq ~loc eq in
    Runtime.return_term e

  | Syntax.CongrEq (c1, c2, c3) ->
    infer c1 >>= as_term ~loc:c1.Location.loc >>= fun jt ->
    infer c2 >>= as_term ~loc:c2.Location.loc >>= fun jlhs ->
    infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jrhs ->
    let eqt = Jdg.reflect_ty_eq ~loc:c1.Location.loc jt
    and eqlhs = Jdg.reflect ~loc:c2.Location.loc jlhs
    and eqrhs = Jdg.reflect  ~loc:c3.Location.loc jrhs in
    let eq = Jdg.congr_eq_ty ~loc eqt eqlhs eqrhs in
    let e = Jdg.refl_of_eq_ty ~loc eq in
    Runtime.return_term e

  | Syntax.CongrRefl (c1, c2) ->
    infer c1 >>= as_term ~loc:c1.Location.loc >>= fun jt ->
    infer c2 >>= as_term ~loc:c2.Location.loc >>= fun je ->
    let eqt = Jdg.reflect_ty_eq ~loc:c1.Location.loc jt
    and eqe = Jdg.reflect ~loc:c2.Location.loc je in
    let eq = Jdg.congr_refl ~loc eqt eqe in
    let e = Jdg.refl_of_eq ~loc eq in
    Runtime.return_term e

  | Syntax.BetaStep (c1, c2, c3, c4, c5) ->
    infer c1 >>= as_atom ~loc:c1.Location.loc >>= fun x ->
    infer c2 >>= as_term ~loc:c2.Location.loc >>= fun ja ->
    infer c3 >>= as_term ~loc:c3.Location.loc >>= fun jb ->
    infer c4 >>= as_term ~loc:c4.Location.loc >>= fun jbody ->
    infer c5 >>= as_term ~loc:c5.Location.loc >>= fun jarg ->
    let eqa = Jdg.reflect_ty_eq ~loc:c2.Location.loc ja
    and eqb = Jdg.reflect_ty_eq ~loc:c3.Location.loc jb in
    let eq = Jdg.beta ~loc eqa x x eqb jbody jarg in
    let e = Jdg.refl_of_eq ~loc eq in
    Runtime.return_term e

  | Syntax.String s ->
    Runtime.return (Runtime.mk_string s)

  | Syntax.Occurs (c1,c2) ->
    infer c1 >>= as_atom ~loc >>= fun a ->
    infer c2 >>= as_term ~loc >>= fun j ->
    begin match Jdg.occurs a j with
      | Some jx ->
        let j = Jdg.term_of_ty (Jdg.atom_ty jx) in
        Runtime.return (Predefined.from_option (Some (Runtime.mk_term j)))
      | None ->
        Runtime.return (Predefined.from_option None)
    end

  | Syntax.Context c ->
    infer c >>= as_term ~loc >>= fun j ->
    let ctx = Jdg.contextof j in
    let xts = Jdg.Ctx.elements ctx in
    let js = List.map (fun j -> Runtime.mk_term (Jdg.atom_term ~loc j)) xts in
    Runtime.return (Predefined.mk_list js)

  | Syntax.Natural c ->
    infer c >>= as_term ~loc >>= fun j ->
    Runtime.lookup_typing_signature >>= fun signature ->
    let eq = Jdg.natural_eq ~loc signature j in
    let e = Jdg.refl_of_eq_ty ~loc eq in
    Runtime.return_term e

and check_default ~loc v t_check =
  as_term ~loc v >>= fun je ->
  Equal.coerce ~loc je t_check >>=
    begin function
      | Some je -> Runtime.return je
      | None -> Runtime.(error ~loc (TypeMismatchCheckingMode (je, t_check)))
  end

and check ({Location.thing=c';loc} as c) t_check =
  match c' with
  | Syntax.Type
  | Syntax.Bound _
  | Syntax.Function _
  | Syntax.Handler _
  | Syntax.Ascribe _
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
  | Syntax.CongrProd _ | Syntax.CongrApply _ | Syntax.CongrLambda _ | Syntax.CongrEq _ | Syntax.CongrRefl _
  | Syntax.BetaStep _
  | Syntax.Ref _
  | Syntax.Lookup _
  | Syntax.Update _
  | Syntax.String _
  | Syntax.Occurs _
  | Syntax.Context _
  | Syntax.Natural _ ->
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

  | Syntax.Lambda (x,u,c) ->
    check_lambda ~loc t_check x u c

  | Syntax.Refl c ->
    Equal.as_eq ~loc t_check >>= begin function
      | None -> Runtime.(error ~loc (EqualityTypeExpected t_check))
      | Some (eq, e1, e2) ->
        let t = Jdg.typeof e1 in
        check c t >>= fun e ->
        Equal.equal ~loc e e1 >>= begin function
          | None -> Runtime.(error ~loc (EqualityFail (e, e1)))
          | Some eq1 ->
            Equal.equal ~loc e e2 >>= begin function
              | None -> Runtime.(error ~loc (EqualityFail (e, e2)))
              | Some eq2 ->
                let j = Jdg.mk_refl ~loc eq1 eq2 in
                let j = Jdg.convert ~loc j (Jdg.symmetry_ty eq) in
                Runtime.return j
              end
          end
      end

and check_lambda ~loc t_check x u c =
  Equal.as_prod ~loc t_check >>= function
    | None -> Runtime.(error ~loc (ProductExpected t_check))
    | Some (eq, a, b) ->
      begin match u with
        | Some u ->
          check_ty u >>= fun ju ->
          Equal.equal_ty ~loc:(u.Location.loc) ju (Jdg.atom_ty a) >>= begin function
            | Some equ -> Runtime.return (ju, equ)
            | None ->
              Runtime.(error ~loc:(u.Location.loc) (AnnotationMismatch (ju, (Jdg.atom_ty a))))
            end
        | None ->
          let ju = Jdg.atom_ty a in
          let equ = Jdg.reflexivity_ty ju in
          Runtime.return (ju, equ)
      end >>= fun (ju, equ) -> (* equ : ju == typeof a *)
      Runtime.add_free ~loc x ju (fun jy ->
      Predefined.add_abstracting (Jdg.atom_term ~loc jy)
      (let b = Jdg.substitute_ty ~loc b a (Jdg.convert ~loc (Jdg.atom_term ~loc jy) equ) in
      check c b >>= fun e ->
      jdg_form ~loc (Jdg.Lambda (jy, e)) >>= fun lam ->
      let eq_prod = Jdg.congr_prod_ty ~loc equ jy a (Jdg.reflexivity_ty b) in
      let lam = Jdg.convert ~loc lam eq_prod in
      let lam = Jdg.convert ~loc lam (Jdg.symmetry_ty eq) in
      Runtime.return lam))

and apply ~loc h c =
  Equal.coerce_fun ~loc h >>= function
    | Some (h, a, _) ->
      check c (Jdg.atom_ty a) >>= fun e ->
      jdg_form ~loc (Jdg.Apply (h, e)) >>= fun j ->
      Runtime.return_term j
    | None ->
       Runtime.(error ~loc (FunctionExpected h))

and sequence ~loc v =
  match v with
    | Runtime.Tuple [] -> Runtime.return ()
    | _ ->
      Runtime.lookup_penv >>= fun penv ->
      Print.warning "%t: Sequence:@ The value %t should be ()" (Location.print loc) (Runtime.print_value ~penv v);
      Runtime.return ()

and let_bind : 'a. _ -> 'a Runtime.comp -> 'a Runtime.comp = fun xcs cmd ->
  let rec fold vs = function
    | [] ->
      (* parallel let: only bind at the end *)
      List.fold_left  (fun cmd v -> Runtime.add_bound v cmd) cmd vs
    | (_, _, c) :: xcs ->
      infer c >>= fun v ->
      fold (v :: vs) xcs
    in
  fold [] xcs

and letrec_bind : 'a. _ -> 'a Runtime.comp -> 'a Runtime.comp = fun fxcs ->
  let gs =
    List.map
      (fun (_, _, _, c) -> (fun v -> Runtime.add_bound v (infer c)))
      fxcs
  in
  Runtime.add_bound_rec gs

(* [match_cases loc cases eval v] tries for each case in [cases] to match [v]
   and if successful continues on the computation using [eval] with the pattern variables bound. *)
and match_cases : type a. loc:_ -> _ -> ('annot Syntax.comp -> a Runtime.comp) -> _ -> a Runtime.comp
 = fun ~loc cases eval v ->
  let rec fold = function
    | [] ->
      Runtime.lookup_penv >>= fun penv ->
      Runtime.(error ~loc (MatchFail v))
    | (xs, p, c) :: cases ->
      Matching.match_pattern p v >>= begin function
        | Some vs ->
          let rec bind = function
            | [] -> eval c
            | v::vs ->
              Runtime.add_bound v (bind vs)
          in
          bind vs
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
          let rec bind = function
            | [] -> infer c
            | v::vs ->
              Runtime.add_bound v (bind vs)
          in
          bind vs
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

let comp_ty c =
  let r = check_ty c in
  Runtime.top_handle ~loc:(c.Location.loc) r

let comp_handle (xs,y,c) =
  Runtime.top_return_closure (fun (vs,checking) ->
      let rec bind = function
        | [] ->
           begin match y with
           | Some _ ->
              let checking = match checking with
                | Some jt -> Some (Runtime.mk_term (Jdg.term_of_ty jt))
                | None -> None
              in
              let vy = Predefined.from_option checking in
              Runtime.add_bound vy (infer c)
           | None -> infer c
           end
        | v::vs -> Runtime.add_bound v (bind vs)
      in
      bind vs)

(** Toplevel commands *)

let (>>=) = Runtime.top_bind
let return = Runtime.top_return

let rec mfold f acc = function
  | [] -> return acc
  | x::rem -> f acc x >>= fun acc ->
     mfold f acc rem

let toplet_bind ~loc ~quiet ~print_annot xcs =
  let rec fold xvs = function
    | [] ->
       (* parallel let: only bind at the end *)
       List.fold_left
         (fun cmd (x, v) -> Runtime.add_topbound v >>= fun () -> cmd)
         (return ())
         xvs
    | (x, s, c) :: xcs ->
       comp_value c >>= fun v ->
       fold ((x, v) :: xvs) xcs
  in
  fold [] xcs >>= fun () ->
  begin if not quiet then
    Format.printf "%t@." (Print.sequence
      (fun (x, annot, _) ppf -> Format.fprintf ppf "@[<hov 2>val %t :@ %t@]@." (Name.print_ident x) (print_annot annot))
      ""
      xcs)
  end;
  return ()

let topletrec_bind ~loc ~quiet ~print_annot fxcs =
  let gs =
    List.map
      (fun (_, _, _, c) -> (fun v -> Runtime.add_bound v (infer c)))
      fxcs
  in
  Runtime.add_topbound_rec gs >>= fun () ->
  begin if not quiet then
    Format.printf "%t@." (Print.sequence
      (fun (f, _, annot, _) ppf -> Format.fprintf ppf "@[<hov 2>val %t :@ %t@]@." (Name.print_ident f) (print_annot annot))
      ""
      fxcs)
  end;
  return ()

type error =
  | RuntimeError of TT.print_env * Runtime.error
  | JdgError of TT.print_env * Jdg.error

exception Error of error Location.located

let error ~loc err = Pervasives.raise (Error (Location.locate err loc))

let print_error err ppf =
  match err with
    | RuntimeError (penv, err) -> Runtime.print_error ~penv err ppf
    | JdgError (penv, err) -> Jdg.print_error ~penv err ppf

let rec toplevel ~quiet ~print_annot {Location.thing=c;loc} =
  Runtime.catch (lazy (match c with

    | Syntax.DefMLType lst
    | Syntax.DefMLTypeRec lst ->
      (if not quiet then Format.printf "ML type%s %t declared.@.@." (match lst with [_] -> "" | _ -> "s") (Print.sequence (fun (t,_) -> Name.print_ident t) " " lst));
      return ()

    | Syntax.DeclOperation (x, k) ->
       if not quiet then Format.printf "Operation %t is declared.@.@." (Name.print_ident x) ;
       return ()

    | Syntax.DeclConstants (xs, c) ->
      comp_ty c >>= fun t ->
      let t = Jdg.is_closed_ty ~loc t in
      let rec fold = function
        | [] -> (if not quiet then Format.printf "@."); return ()
        | x :: xs ->
          Runtime.add_constant ~loc x t >>= fun () ->
          (if not quiet then Format.printf "Constant %t is declared.@." (Name.print_ident x) ;
           fold xs)
      in
      fold xs

    | Syntax.TopHandle lst ->
       mfold (fun () (op, xc) ->
           comp_handle xc >>= fun f ->
           Runtime.add_handle op f) () lst

    | Syntax.TopLet xcs ->
      let print_annot = print_annot () in
      toplet_bind ~loc ~quiet ~print_annot xcs

    | Syntax.TopLetRec fxcs ->
      let print_annot = print_annot () in
      topletrec_bind ~loc ~quiet ~print_annot fxcs

    | Syntax.TopDynamic (x, annot, c) ->
       comp_value c >>= fun v ->
       Runtime.add_dynamic ~loc x v

    | Syntax.TopNow (x,c) ->
       comp_value c >>= fun v ->
       Runtime.top_now ~loc x v

    | Syntax.TopDo c ->
       comp_value c >>= fun v ->
       Runtime.top_lookup_penv >>= fun penv ->
       (begin if not quiet then
            Format.printf "%t@.@." (Runtime.print_value ~penv v)
        end;
        return ())

    | Syntax.TopFail c ->
       Runtime.catch (lazy (comp_value c)) >>= begin function

       | Runtime.CaughtRuntime {Location.thing=err; loc}  ->
         Runtime.top_lookup_penv >>= fun penv ->
         (if not quiet then Format.printf "Successfully failed command with runtime error:@.%t:@ %t@.@."
                                          (Location.print loc)
                                          (Runtime.print_error ~penv err));
         return ()

       | Runtime.CaughtJdg {Location.thing=err; loc}  ->
         Runtime.top_lookup_penv >>= fun penv ->
         (if not quiet then Format.printf "Successfully failed command with judgment error:@.%t:@ %t@.@."
                                          (Location.print loc)
                                          (Jdg.print_error ~penv err));
         return ()

       | Runtime.Value v ->
         Runtime.error ~loc (Runtime.FailureFail v)
       end

    | Syntax.Included lst ->
      mfold (fun () (fn, cmds) ->
          (if not quiet then Format.printf "#including %s@." fn);
          mfold (fun () cmd -> toplevel ~quiet:true ~print_annot cmd) () cmds >>= fun () ->
          (if not quiet then Format.printf "#processed %s@." fn);
          return ())
        () lst

    | Syntax.Verbosity i -> Config.verbosity := i; return ()
  )) >>= function
  | Runtime.CaughtJdg {Location.thing=err; loc}  ->
    Runtime.top_lookup_penv >>= fun penv ->
    error ~loc (JdgError (penv, err))

  | Runtime.CaughtRuntime {Location.thing=err; loc}  ->
    Runtime.top_lookup_penv >>= fun penv ->
    error ~loc (RuntimeError (penv, err))

  | Runtime.Value v -> return v
