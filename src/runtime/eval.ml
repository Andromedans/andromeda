(** Evaluation of computations *)

(** Notation for the monadic bind *)
let (>>=) = Runtime.bind

let return = Runtime.return

let as_is_term_abstraction = Runtime.as_is_term

let as_is_term ~loc v =
  let e = Runtime.as_is_term ~loc v in
  match Jdg.invert_is_term_abstraction e with
  | Jdg.NotAbstract e -> e
  | Jdg.Abstract _ -> Runtime.(error ~loc (IsTermExpected v))

let as_is_type_abstraction = Runtime.as_is_type

let as_is_type ~loc v =
  let t = Runtime.as_is_type ~loc v in
  match Jdg.invert_is_type_abstraction t with
  | Jdg.NotAbstract t -> t
  | Jdg.Abstract _ -> Runtime.(error ~loc (IsTypeExpected v))

let as_eq_type_abstraction = Runtime.as_eq_type

let as_eq_term_abstraction = Runtime.as_eq_term

let as_atom ~loc v =
  Runtime.lookup_signature >>= fun sgn ->
  let j = as_is_term ~loc v in
  match Jdg.invert_is_term sgn j with
    | Jdg.TermAtom x -> return x
    | (Jdg.TermConstructor _ | Jdg.TermConvert _) -> Runtime.(error ~loc (ExpectedAtom j))

(* as_handler: loc:Location.t -> Runtime.value -> Runtime.handler Runtime.comp *)
let as_handler ~loc v =
  let e = Runtime.as_handler ~loc v in
  return e

(* as_ref: loc:Location.t -> Runtime.value -> Runtime.ref Runtime.comp *)
let as_ref ~loc v =
  let e = Runtime.as_ref ~loc v in
  return e

let as_dyn ~loc v =
  let e = Runtime.as_dyn ~loc v in
  return e

(** Evaluate a computation -- infer mode. *)
(*   infer : Rsyntax.comp -> Runtime.value Runtime.comp *)
let rec infer {Location.thing=c'; loc} =
  let not_abstr e = Jdg.form_abstraction (Jdg.NotAbstract e) in
  match c' with
    | Rsyntax.Bound i ->
       Runtime.lookup_bound ~loc i

    | Rsyntax.Function (_, c) ->
       let f v =
         Runtime.add_bound v
           (infer c)
       in
       Runtime.return_closure f

    | Rsyntax.AMLConstructor (t, cs) ->
       let rec fold vs = function
         | [] ->
            let vs = List.rev vs in
            return vs
         | c :: cs ->
            infer c >>= fun v ->
            fold (v :: vs) cs
       in
       fold [] cs >>= fun vs ->
       let v = Runtime.mk_tag t vs in
       return v

    | Rsyntax.IsTypeConstructor (c, cs) ->
       (* XXX premises should really be run in checking mode!!! *)
       infer_premises [] cs >>= fun premises ->
       Runtime.lookup_signature >>= fun sgn ->
       let e = Jdg.form_is_type_rule sgn c premises in
       let v = Runtime.mk_is_type (not_abstr e) in
       return v

    | Rsyntax.IsTermConstructor (c, cs) ->
       infer_premises [] cs >>= fun premises ->
       Runtime.lookup_signature >>= fun sgn ->
       let e = Jdg.form_is_term_rule sgn c premises in
       let v = Runtime.mk_is_term (not_abstr e) in
       return v

    | Rsyntax.EqTypeConstructor (c, cs) ->
       infer_premises [] cs >>= fun premises ->
       Runtime.lookup_signature >>= fun sgn ->
       let e = Jdg.form_eq_type_rule sgn c premises in
       let v = Runtime.mk_eq_type (not_abstr e) in
       return v

    | Rsyntax.EqTermConstructor (c, cs) ->
       infer_premises [] cs >>= fun premises ->
       Runtime.lookup_signature >>= fun sgn ->
       let e = Jdg.form_eq_term_rule sgn c premises in
       let v = Runtime.mk_eq_term (not_abstr e) in
       return v

    | Rsyntax.Tuple cs ->
      let rec fold vs = function
        | [] -> return (Runtime.mk_tuple (List.rev vs))
        | c :: cs -> (infer c >>= fun v -> fold (v :: vs) cs)
      in
      fold [] cs

    | Rsyntax.Handler {Rsyntax.handler_val; handler_ops; handler_finally} ->
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

  | Rsyntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op vs
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Rsyntax.With (c1, c2) ->
     infer c1 >>= as_handler ~loc >>= fun h ->
     Runtime.handle_comp h (infer c2)

  | Rsyntax.Let (xcs, c) ->
     let_bind ~loc xcs (infer c)

  | Rsyntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (infer c)

  | Rsyntax.Now (x,c1,c2) ->
     let xloc = x.Location.loc in
     infer x >>= as_dyn ~loc:xloc >>= fun x ->
     infer c1 >>= fun v ->
     Runtime.now x v (infer c2)

  | Rsyntax.Current c ->
     infer c >>= as_dyn ~loc:(c.Location.loc) >>= fun x ->
     Runtime.lookup_dyn x

  | Rsyntax.Ref c ->
     infer c >>= fun v ->
     Runtime.mk_ref v

  | Rsyntax.Lookup c ->
     infer c >>= as_ref ~loc >>= fun x ->
     Runtime.lookup_ref x

  | Rsyntax.Update (c1, c2) ->
     infer c1 >>= as_ref ~loc >>= fun x ->
     infer c2 >>= fun v ->
     Runtime.update_ref x v >>= fun () ->
     Runtime.return_unit

  | Rsyntax.Sequence (c1, c2) ->
     infer c1 >>= fun v ->
     sequence ~loc v >>= fun () ->
     infer c2

  | Rsyntax.Assume ((x, c1), c2) ->
     check_is_type c1 >>= fun t ->
     Runtime.add_free x t (fun _ -> infer c2)

  | Rsyntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases infer

  | Rsyntax.Ascribe (c1, c2) ->
     check_is_type_abstraction c2 >>= fun t ->
     check c1 t >>=
     Runtime.return_is_term

  | Rsyntax.Abstract (x, None, _) ->
    Runtime.(error ~loc (UnannotatedAbstract x))

  | Rsyntax.Abstract (x, Some u, c) ->
     check_is_type u >>= fun ju ->
     Runtime.add_free x ju (fun jy ->
         let vy = Jdg.form_is_term_atom jy in
         let vy = Jdg.form_abstraction (Jdg.NotAbstract vy) in
         let abstract j = Jdg.form_abstraction (Jdg.Abstract (jy, j)) in

         Predefined.add_abstracting
           vy
           begin infer c >>=
             function

             | Runtime.IsType jdg -> Runtime.return_is_type (abstract jdg)

             | Runtime.IsTerm jdg -> Runtime.return_is_term (abstract jdg)

             | Runtime.EqType jdg -> Runtime.return_eq_type (abstract jdg)

             | Runtime.EqTerm jdg -> Runtime.return_eq_term (abstract jdg)

             | (Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ |
                Runtime.Tuple _ | Runtime.Ref _ | Runtime.Dyn _ |
                Runtime.String _) as v ->
                Runtime.(error ~loc (JudgementExpected v))

           end)

  | Rsyntax.Yield c ->
    infer c >>= fun v ->
    Runtime.continue ~loc v

  | Rsyntax.Apply (c1, c2) ->
    infer c1 >>= begin function
      | Runtime.Closure f ->
        infer c2 >>= fun v ->
        Runtime.apply_closure f v
      | Runtime.IsTerm _ | Runtime.IsType _ | Runtime.EqTerm _ | Runtime.EqType _ |
        Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
        Runtime.Ref _ | Runtime.Dyn _ | Runtime.String _ as h ->
        Runtime.(error ~loc (Inapplicable h))
    end

  | Rsyntax.String s ->
    return (Runtime.mk_string s)

  | Rsyntax.OccursIsTypeAbstraction (c1, c2) ->
     check_is_type_abstraction c2 >>= fun abstr ->
     occurs Jdg.occurs_is_type_abstraction c1 abstr

  | Rsyntax.OccursIsTermAbstraction (c1,c2) ->
     check_is_term_abstraction c2 >>= fun abstr ->
     occurs Jdg.occurs_is_term_abstraction c1 abstr

  | Rsyntax.OccursEqTypeAbstraction (c1, c2) ->
     check_eq_type_abstraction c2 >>= fun abstr ->
     occurs Jdg.occurs_eq_type_abstraction c1 abstr

  | Rsyntax.OccursEqTermAbstraction (c1, c2) ->
     check_eq_term_abstraction c2 >>= fun abstr ->
     occurs Jdg.occurs_eq_term_abstraction c1 abstr


  | Rsyntax.Context c ->
    check_is_term c >>= fun j ->
    let ctx = Jdg.contextof j in
    let xts = Jdg.Ctx.elements ctx in
    let js = List.map (fun j -> Runtime.mk_is_term (Jdg.atom_is_term ~loc j)) xts in
    return (Predefined.mk_list js)

  | Rsyntax.Natural c ->
    check_is_term c >>= fun j ->
    Runtime.lookup_signature >>= fun signature ->
    let eq = Jdg.natural_eq_type ~loc signature j in
    Runtime.return_eq_type eq

(* XXX premises should really be run in checking mode!!! *)
and infer_premises ps_out = function
  | [] -> return (List.rev ps_out)
  | p :: ps -> infer p >>= as_premise >>= fun p ->
     infer_premises (p :: ps_out) ps

and occurs
  : 'a . (Jdg.is_atom -> 'a Jdg.abstraction -> bool)
    -> Rsyntax.comp
    -> 'a Jdg.abstraction -> Runtime.value Runtime.comp
  = fun occurs_abstr c1 abstr ->
  check_atom c1 >>= fun a ->
  begin match occurs_abstr a abstr with
  | true ->
     let t = Jdg.type_of_atom a in
     let t = Runtime.mk_is_type (Jdg.form_abstraction (Jdg.NotAbstract t)) in
     return (Predefined.from_option (Some t))
  | false ->
     return (Predefined.from_option None)
  end

and check_default ~loc v t_check =
  let je = as_is_term_abstraction ~loc v in
  Equal.coerce ~loc je t_check >>=
    begin function
      | Some je -> return je
      | None -> Runtime.(error ~loc (TypeMismatchCheckingMode (je, t_check)))
  end

and check_premises premises t_premises =

  let rec fold ps_out ps ts =
    match ps, ts with

    | [], [] ->
       let ps_out = List.rev ps_out in
       return ps_out

    | p :: ps, t :: ts ->
       check_premise p t >>= fun p ->
       fold (p :: ps_out) ps ts

    | [], _::_ | _::_, [] ->
       (* desugar made sure this cannot happen *)
       assert false
  in
  fold [] premises t_premises

and check_premise c t =
  check c t >>= fun e -> as_premise (Runtime.mk_is_term e)

and as_premise = function
  | Runtime.IsType t -> return (Jdg.PremiseIsType t)
  | Runtime.IsTerm e -> return (Jdg.PremiseIsTerm e)
  | Runtime.EqType eq -> return (Jdg.PremiseEqType eq)
  | Runtime.EqTerm eq -> return (Jdg.PremiseEqTerm eq)
  | (Runtime.Closure _ | Runtime.Handler _ | Runtime.Tag _ | Runtime.Tuple _ |
     Runtime.Ref _| Runtime.Dyn _| Runtime.String _) ->
     assert false


(* Rsyntax.comp -> Jdg.is_type -> Jdg.is_term Runtime.comp *)
and check ({Location.thing=c';loc} as c) t_check =
  match c' with

  (* for these we switch to infer mode *)
  | Rsyntax.Bound _
  | Rsyntax.Function _
  | Rsyntax.Handler _
  | Rsyntax.Ascribe _
  | Rsyntax.AMLConstructor _
  | Rsyntax.IsTypeConstructor _
  | Rsyntax.IsTermConstructor _
  | Rsyntax.EqTypeConstructor _
  | Rsyntax.EqTermConstructor _
  | Rsyntax.Tuple _
  | Rsyntax.With _
  | Rsyntax.Yield _
  | Rsyntax.Apply _
  | Rsyntax.Ref _
  | Rsyntax.Lookup _
  | Rsyntax.Update _
  | Rsyntax.Current _
  | Rsyntax.String _
  | Rsyntax.OccursIsTypeAbstraction _
  | Rsyntax.OccursIsTermAbstraction _
  | Rsyntax.OccursEqTypeAbstraction _
  | Rsyntax.OccursEqTermAbstraction _
  | Rsyntax.Context _
  | Rsyntax.Natural _ ->
    infer c >>= fun v ->
    check_default ~loc v t_check

  | Rsyntax.Operation (op, cs) ->
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

  | Rsyntax.Let (xcs, c) ->
     let_bind ~loc xcs (check c t_check)

  | Rsyntax.Sequence (c1,c2) ->
    infer c1 >>= fun v ->
    sequence ~loc v >>= fun () ->
    check c2 t_check

  | Rsyntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (check c t_check)

  | Rsyntax.Now (x,c1,c2) ->
     let xloc = x.Location.loc in
     infer x >>= as_dyn ~loc:xloc >>= fun x ->
     infer c1 >>= fun v ->
     Runtime.now x v (check c2 t_check)

  | Rsyntax.Assume ((x, t), c) ->
     check_is_type t >>= fun t ->
     Runtime.add_free x t (fun _ ->
     check c t_check)

  | Rsyntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases (fun c -> check c t_check)

  | Rsyntax.Abstract (x, u, c) ->
    check_abstract ~loc t_check x u c

and check_abstract ~loc t_check x u c =
  Runtime.lookup_signature >>= fun sgn ->
  match Jdg.invert_is_type sgn t_check with

  | Jdg.TypeConstructor _ ->
     Runtime.(error ~loc (AbstractTyExpected t_check))

  | Jdg.AbstractTy (a, b) ->
     begin match u with
     | Some u ->
        check_is_type u >>= fun ju ->
        Equal.equal_ty ~loc:(u.Location.loc) ju (Jdg.type_of_atom a) >>=
          begin function
            | Some equ -> return (ju, equ)
            | None ->
               Runtime.(error ~loc:(u.Location.loc) (AnnotationMismatch (ju, (Jdg.type_of_atom a))))
          end
     | None ->
        let ju = Jdg.type_of_atom a in
        let equ = Jdg.reflexivity_ty ju in
        return (ju, equ)
     end >>= fun (ju, equ) -> (* equ : ju == typeof a *)
     Runtime.add_free ~loc x ju (
         fun jy -> (* jy is a free variable of type ju *)
         let ja = Jdg.atom_is_term ~loc jy in
         Predefined.add_abstracting ja
           (let b = Jdg.substitute_ty ~loc b a (Jdg.convert ~loc ja equ) in
            check c b >>= fun e ->
            form_is_term ~loc (Jdg.Abstract (jy, e)) >>= fun abstr ->
            let eq_abstr = Jdg.congr_abstract_type ~loc equ jy a (Jdg.reflexivity_ty b) in
            let abstr = Jdg.convert ~loc abstr eq_abstr in
            return abstr))

(* sequence: loc:Location.t -> Runtime.value -> unit Runtime.comp *)
and sequence ~loc v =
  match v with
    | Runtime.Tuple [] -> return ()
    | _ ->
      Runtime.lookup_penv >>= fun penv ->
      Print.warning "%t: Sequence:@ The value %t should be ()" (Location.print loc) (Runtime.print_value ~penv v);
      return ()

and let_bind
  : 'a. loc:Location.t -> Rsyntax.let_clause list -> 'a Runtime.comp -> 'a Runtime.comp
  = fun ~loc clauses cmd ->
  let rec fold vs = function
    | [] ->
      (* parallel let: only bind at the end *)
      List.fold_left (fun cmd v -> Runtime.add_bound v cmd) cmd vs
    | Rsyntax.Let_clause (xs, pt, c) :: clauses ->
       infer c >>= fun v ->
       Matching.match_pattern pt v >>= begin function
        | Some us -> fold (List.rev us @ vs) clauses
        | None ->
           Runtime.lookup_penv >>= fun penv ->
           Runtime.(error ~loc (MatchFail v))
       end

  in
  fold [] clauses

and letrec_bind
  : 'a . Rsyntax.letrec_clause list -> 'a Runtime.comp -> 'a Runtime.comp
  = fun fxcs ->
  let gs =
    List.map
      (fun (Rsyntax.Letrec_clause (_, _, _, c)) -> (fun v -> Runtime.add_bound v (infer c)))
      fxcs
  in
  Runtime.add_bound_rec gs

(* [match_cases loc cases eval v] tries for each case in [cases] to match [v]
   and if successful continues on the computation using [eval] with the pattern variables bound. *)
and match_cases
  : 'a . loc:Location.t -> Rsyntax.match_case list -> (Rsyntax.comp -> 'a Runtime.comp)
         -> Runtime.value -> 'a Runtime.comp
  = fun ~loc cases eval v ->
  let rec fold = function
    | [] ->
      Runtime.lookup_penv >>= fun penv ->
      Runtime.(error ~loc (MatchFail v))
    | (p, c) :: cases ->
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
    | (ps, ptopt, c) :: cases ->
      Matching.match_op_pattern ps ptopt vs checking >>=
        begin function
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

and check_is_type c : Jdg.is_type Runtime.comp =
  infer c >>= fun v -> return (as_is_type ~loc:c.Location.loc v)

and check_is_type_abstraction c =
  infer c >>= fun v -> return (as_is_type_abstraction ~loc:c.Location.loc v)

and check_is_term c =
  infer c >>= fun v -> return (as_is_term ~loc:c.Location.loc v)

and check_is_term_abstraction c =
  infer c >>= fun v -> return (as_is_term_abstraction ~loc:c.Location.loc v)

and check_eq_type_abstraction c =
  infer c >>= fun v -> return (as_eq_type_abstraction ~loc:c.Location.loc v)

and check_eq_term_abstraction c =
  infer c >>= fun v -> return (as_eq_term_abstraction ~loc:c.Location.loc v)

and check_atom c =
  infer c >>= fun v -> (as_atom ~loc:c.Location.loc v)

(** Move to toplevel monad *)

(* comp_value: 'a Rsyntax.comp -> Runtime.value Runtime.toplevel *)
let comp_value c =
  let r = infer c in
  Runtime.top_handle ~loc:c.Location.loc r

(* comp_ty: 'a Rsyntax.comp -> Jdg.is_type Runtime.toplevel *)
let comp_ty c =
  let r = check_is_type c in
  Runtime.top_handle ~loc:(c.Location.loc) r

let comp_handle (xs,y,c) =
  Runtime.top_return_closure (fun (vs,checking) ->
      let rec bind = function
        | [] ->
           begin match y with
           | Some _ ->
              let checking = match checking with
                | Some jt -> Some (Runtime.mk_is_type jt)
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

let toplet_bind ~loc ~quiet ~print_annot clauses =
  let rec fold vs = function
    | [] ->
       (* parallel let: only bind at the end *)
       List.fold_left
         (fun cmd v -> Runtime.add_topbound v >>= fun () -> cmd)
         (return ())
         vs

    | Rsyntax.Let_clause (_, pt, c) :: clauses ->
       comp_value c >>= fun v ->
       Matching.top_match_pattern pt v >>= begin function
        | None -> Runtime.error ~loc (Runtime.MatchFail v)
        | Some us -> fold (List.rev us @ vs) clauses
       end
  in
  fold [] clauses >>= fun () ->
    if not quiet then
      (List.iter (function
       | Rsyntax.Let_clause (xts, _, _) ->
          List.iter
            (fun (x, sch) -> Format.printf "@[<hov 2>val %t :>@ %t@]@."
                                               (Name.print_ident x)
                                               (print_annot sch))
               xts)
         clauses ;
         Format.printf "@.") ;
    return ()

let topletrec_bind ~loc ~quiet ~print_annot fxcs =
  let gs =
    List.map
      (fun (Rsyntax.Letrec_clause (_, _, _, c)) v -> Runtime.add_bound v (infer c))
      fxcs
  in
  Runtime.add_topbound_rec gs >>= fun () ->
  if not quiet then
    (List.iter
      (fun (Rsyntax.Letrec_clause (f, _, annot, _)) ->
        Format.printf "@[<hov 2>val %t :>@ %t@]@."
                      (Name.print_ident f)
                      (print_annot annot))
      fxcs ;
     Format.printf "@.") ;
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
  Runtime.catch ~loc (lazy (match c with

    | Rsyntax.DefMLType lst

    | Rsyntax.DefMLTypeRec lst ->
      (if not quiet then
         Format.printf "ML type%s %t declared.@.@."
                       (match lst with [_] -> "" | _ -> "s")
                       (Print.sequence (fun (t,_) -> Name.print_ident t)
                                       " " lst)) ;
      return ()

    | Rsyntax.DeclOperation (x, k) ->
       (if not quiet then
         Format.printf "Operation %t is declared.@.@."
                       (Name.print_ident x)) ;
       return ()

    | Rsyntax.DeclExternal (x, sch, s) ->
       begin
         match External.lookup s with
         | None -> Runtime.error ~loc (Runtime.UnknownExternal s)
         | Some v ->
            Runtime.add_topbound v >>= (fun () ->
             if not quiet then
               Format.printf "@[<hov 2>external %t :@ %t = \"%s\"@]@.@."
                             (Name.print_ident x)
                             (print_annot () sch)
                             s ;
             return ())
       end

    | Rsyntax.TopHandle lst ->
       Runtime.top_fold (fun () (op, xc) ->
           comp_handle xc >>= fun f ->
           Runtime.add_handle op f) () lst

    | Rsyntax.TopLet clauses ->
      let print_annot = print_annot () in
      toplet_bind ~loc ~quiet ~print_annot clauses

    | Rsyntax.TopLetRec fxcs ->
      let print_annot = print_annot () in
      topletrec_bind ~loc ~quiet ~print_annot fxcs

    | Rsyntax.TopDynamic (x, annot, c) ->
       comp_value c >>= fun v ->
       Runtime.add_dynamic ~loc x v

    | Rsyntax.TopNow (x,c) ->
       let xloc = x.Location.loc in
       comp_value x >>= fun x ->
       let x = Runtime.as_dyn ~loc:xloc x in
       comp_value c >>= fun v ->
       Runtime.top_now x v

    | Rsyntax.TopDo c ->
       comp_value c >>= fun v ->
       Runtime.top_lookup_penv >>= fun penv ->
       (begin if not quiet then
            Format.printf "%t@.@." (Runtime.print_value ~penv v)
        end;
        return ())

    | Rsyntax.TopFail c ->
       Runtime.catch ~loc (lazy (comp_value c)) >>= begin function

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

       | Runtime.Result r ->
         Runtime.error ~loc (Runtime.FailureFail r)
       end

    | Rsyntax.Included lst ->
      Runtime.top_fold (fun () (fn, cmds) ->
          (if not quiet then Format.printf "#including %s@." fn);
          Runtime.top_fold (fun () cmd -> toplevel ~quiet:true ~print_annot cmd) () cmds >>= fun () ->
          (if not quiet then Format.printf "#processed %s@." fn);
          return ())
        () lst

    | Rsyntax.Verbosity i -> Config.verbosity := i; return ()
  )) >>= function
  | Runtime.CaughtJdg {Location.thing=err; loc}  ->
    Runtime.top_lookup_penv >>= fun penv ->
    error ~loc (JdgError (penv, err))

  | Runtime.CaughtRuntime {Location.thing=err; loc}  ->
    Runtime.top_lookup_penv >>= fun penv ->
    error ~loc (RuntimeError (penv, err))

  | Runtime.Result r -> return r
