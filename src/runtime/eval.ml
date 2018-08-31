(** Evaluation of computations *)

(** Notation for the monadic bind *)
let (>>=) = Runtime.bind

(** A computation filter that verifies the result is a term,
    and fails otherwise. *)
(* as_is_term : loc:Location.t -> Runtime.value -> Jdg.is_term Runtime.comp *)
let as_is_term ~loc v =
  let e = Runtime.as_is_term ~loc v in
    Runtime.return e

(** A computation filter that verifies the result is a type,
    and fails otherwise. *)
(* as_is_type : loc:Location.t -> Runtime.value -> Jdg.is_term Runtime.comp *)
let as_is_type ~loc v =
  let e = Runtime.as_is_type ~loc v in
    Runtime.return e

let as_eq_type ~loc v =
  let e = Runtime.as_eq_type ~loc v in
    Runtime.return e

let as_eq_term ~loc v =
  let e = Runtime.as_eq_term ~loc v in
    Runtime.return e

let as_atom ~loc v =
  as_is_term ~loc v >>= fun j ->
  match Jdg.invert_is_term j with
    | Jdg.Atom x -> Runtime.return x
    | _ -> Runtime.(error ~loc (ExpectedAtom j))

(* as_handler: loc:Location.t -> Runtime.value -> Runtime.handler Runtime.comp *)
let as_handler ~loc v =
  let e = Runtime.as_handler ~loc v in
  Runtime.return e

(* as_ref: loc:Location.t -> Runtime.value -> Runtime.ref Runtime.comp *)
let as_ref ~loc v =
  let e = Runtime.as_ref ~loc v in
  Runtime.return e

let as_dyn ~loc v =
  let e = Runtime.as_dyn ~loc v in
  Runtime.return e

(** Form a term judgement *)
(* loc:Location.t -> Jdg.shape -> Jdg.is_term Runtime.comp *)
let form_is_term ~loc s =
  Runtime.lookup_typing_signature >>= fun signature ->
  Runtime.return (Jdg.form_is_term ~loc signature s)

(** Form a type judgement *)
(* loc:Location.t -> Jdg.shape_ty -> Jdg.is_type Runtime.comp *)
let form_is_type ~loc s =
  Runtime.lookup_typing_signature >>= fun signature ->
  Runtime.return (Jdg.form_is_type ~loc signature s)

(** Evaluate a computation -- infer mode. *)
(*   infer : Rsyntax.comp -> Runtime.value Runtime.comp *)
let rec infer {Location.thing=c'; loc} =
  match c' with
    | Rsyntax.Bound i ->
       Runtime.lookup_bound ~loc i

    | Rsyntax.Type ->
      form_is_type ~loc Jdg.Type >>=
      Runtime.return_is_type

    | Rsyntax.El c ->
       check_is_term c >>= fun e ->
       form_is_type ~loc (Jdg.El e) >>=
       Runtime.return_is_type

    | Rsyntax.Function (_, c) ->
       let f v =
         Runtime.add_bound v
           (infer c)
       in
       Runtime.return_closure f

    | Rsyntax.Constructor (t, cs) ->
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

    | Rsyntax.Tuple cs ->
      let rec fold vs = function
        | [] -> Runtime.return (Runtime.mk_tuple (List.rev vs))
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
     Runtime.add_free ~loc x t (fun _ ->
       infer c2)

  | Rsyntax.Where (c1, c2, c3) ->
    check_atom c2 >>= fun a ->
    check_is_term c1 >>= fun je ->
    begin match Jdg.occurs a je with
    | None ->
       check c3 (Jdg.atom_is_type a) >>= fun _ ->
       Runtime.return_is_term je
    | Some a ->
       check c3 (Jdg.atom_is_type a) >>= fun js ->
       let j = Jdg.substitute ~loc je a js in
       Runtime.return_is_term j
    end

  | Rsyntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases infer

  | Rsyntax.Ascribe (c1, c2) ->
     check_is_type c2 >>= fun t ->
     check c1 t >>=
     Runtime.return_is_term

  | Rsyntax.Constant x ->
    form_is_term ~loc (Jdg.Constant x) >>=
    Runtime.return_is_term

  | Rsyntax.Abstract (x, None, _) ->
    Runtime.(error ~loc (UnannotatedAbstract x))

  | Rsyntax.Abstract (x, Some u, c) ->
     check_is_type u >>= fun ju ->
     Runtime.add_free ~loc:(u.Location.loc) x ju (fun jy ->
         let vy = Jdg.atom_is_term ~loc:(u.Location.loc) jy in
         Predefined.add_abstracting vy
      (infer c >>= function
       | Runtime.IsTerm je -> form_is_term ~loc (Jdg.Abstract (jy, je)) >>= Runtime.return_is_term
       | Runtime.IsType jt -> form_is_type ~loc (Jdg.AbstractTy (jy, jt)) >>= Runtime.return_is_type
       | (Runtime.EqTerm _ | Runtime.EqType _ | Runtime.Closure _ | Runtime.Handler _ |
          Runtime.Tag _ | Runtime.Tuple _ | Runtime.Ref _ | Runtime.Dyn _ | Runtime.String _) as v ->
          Runtime.(error ~loc (IsTypeOrTermExpected v))
      ))

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

  | Rsyntax.CongrAbstractTy (c1, c2, c3) ->
    check_atom c1 >>= fun x ->
    check_eq_type c2 >>= fun eqa ->
    check_eq_type c3 >>= fun eqb ->
    let eq = Jdg.congr_abstract_type ~loc eqa x x eqb in
    Runtime.return_eq_type eq

  | Rsyntax.CongrAbstract (c1, c2, c3, c4) ->
    check_atom c1 >>= fun x ->
    check_eq_type c2 >>= fun eqa ->
    check_eq_type c3 >>= fun eqb ->
    check_eq_term c4 >>= fun eqbody ->
    let eq = Jdg.congr_abstract_term ~loc eqa x x eqb eqbody in
    Runtime.return_eq_term eq

  | Rsyntax.Reflexivity_term c ->
     check_is_term c >>= fun je ->
     let eq = Jdg.reflexivity je in
     Runtime.return_eq_term eq

  | Rsyntax.Symmetry_term c ->
     check_eq_term c >>= fun jeq ->
     let eq = Jdg.symmetry_term jeq in
     Runtime.return_eq_term eq

  | Rsyntax.Transitivity_term (c1, c2) ->
     check_eq_term c1 >>= fun jeq1 ->
     check_eq_term c2 >>= fun jeq2 ->
     let eq = Jdg.transitivity_term ~loc jeq1 jeq2 in
     Runtime.return_eq_term eq


  | Rsyntax.Reflexivity_type c ->
     check_is_type c >>= fun jt ->
     let eq = Jdg.reflexivity_ty jt in
     Runtime.return_eq_type eq

  | Rsyntax.Symmetry_type c ->
     check_eq_type c >>= fun jeq ->
     let eq = Jdg.symmetry_type jeq in
     Runtime.return_eq_type eq

  | Rsyntax.Transitivity_type (c1, c2) ->
     check_eq_type c1 >>= fun jeq1 ->
     check_eq_type c2 >>= fun jeq2 ->
     let eq = Jdg.transitivity_type ~loc jeq1 jeq2 in
     Runtime.return_eq_type eq

  | Rsyntax.String s ->
    Runtime.return (Runtime.mk_string s)

  | Rsyntax.Occurs (c1,c2) ->
    check_atom c1 >>= fun a ->
    check_is_term c2 >>= fun j ->
    begin match Jdg.occurs a j with
      | Some jx ->
        let j = Jdg.atom_is_type jx in
        Runtime.return (Predefined.from_option (Some (Runtime.mk_is_type j)))
      | None ->
        Runtime.return (Predefined.from_option None)
    end

  | Rsyntax.Context c ->
    check_is_term c >>= fun j ->
    let ctx = Jdg.contextof j in
    let xts = Jdg.Ctx.elements ctx in
    let js = List.map (fun j -> Runtime.mk_is_term (Jdg.atom_is_term ~loc j)) xts in
    Runtime.return (Predefined.mk_list js)

  | Rsyntax.Natural c ->
    check_is_term c >>= fun j ->
    Runtime.lookup_typing_signature >>= fun signature ->
    let eq = Jdg.natural_eq_type ~loc signature j in
    Runtime.return_eq_type eq

and check_default ~loc v t_check =
  as_is_term ~loc v >>= fun je ->
  Equal.coerce ~loc je t_check >>=
    begin function
      | Some je -> Runtime.return je
      | None -> Runtime.(error ~loc (TypeMismatchCheckingMode (je, t_check)))
  end

(* Rsyntax.comp -> Jdg.is_type -> Jdg.is_term Runtime.comp *)
and check ({Location.thing=c';loc} as c) t_check =
  match c' with
  | Rsyntax.Type
  | Rsyntax.El _
  | Rsyntax.Bound _
  | Rsyntax.Function _
  | Rsyntax.Handler _
  | Rsyntax.Ascribe _
  | Rsyntax.Constructor _
  | Rsyntax.Tuple _
  | Rsyntax.Where _
  | Rsyntax.With _
  | Rsyntax.Constant _
  | Rsyntax.Yield _
  | Rsyntax.Apply _
  | Rsyntax.CongrAbstractTy _ | Rsyntax.CongrAbstract _
  | Rsyntax.Reflexivity_term _ | Rsyntax.Reflexivity_type _
  | Rsyntax.Symmetry_term _ | Rsyntax.Symmetry_type _
  | Rsyntax.Transitivity_term _ | Rsyntax.Transitivity_type _
  | Rsyntax.Ref _
  | Rsyntax.Lookup _
  | Rsyntax.Update _
  | Rsyntax.Current _
  | Rsyntax.String _
  | Rsyntax.Occurs _
  | Rsyntax.Context _
  | Rsyntax.Natural _ ->
    (** this is the [check-infer] rule, which applies for all term formers "foo"
        that don't have a "check-foo" rule *)

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
     Runtime.add_free ~loc x t (fun _ ->
     check c t_check)

  | Rsyntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases (fun c -> check c t_check)

  | Rsyntax.Abstract (x, u, c) ->
    check_abstract ~loc t_check x u c

and check_abstract ~loc t_check x u c =
  match Jdg.invert_is_type t_check with

  | (Jdg.TyConstructor _ | Jdg.Type | Jdg.El _) ->
     Runtime.(error ~loc (AbstractTyExpected t_check))

  | Jdg.AbstractTy (a, b) ->
     begin match u with
     | Some u ->
        check_is_type u >>= fun ju ->
        Equal.equal_ty ~loc:(u.Location.loc) ju (Jdg.atom_is_type a) >>=
          begin function
            | Some equ -> Runtime.return (ju, equ)
            | None ->
               Runtime.(error ~loc:(u.Location.loc) (AnnotationMismatch (ju, (Jdg.atom_is_type a))))
          end
     | None ->
        let ju = Jdg.atom_is_type a in
        let equ = Jdg.reflexivity_ty ju in
        Runtime.return (ju, equ)
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
            Runtime.return abstr))

(* sequence: loc:Location.t -> Runtime.value -> unit Runtime.comp *)
and sequence ~loc v =
  match v with
    | Runtime.Tuple [] -> Runtime.return ()
    | _ ->
      Runtime.lookup_penv >>= fun penv ->
      Print.warning "%t: Sequence:@ The value %t should be ()" (Location.print loc) (Runtime.print_value ~penv v);
      Runtime.return ()

and let_bind : 'a. loc:_ -> _ -> 'a Runtime.comp -> 'a Runtime.comp =
  fun ~loc clauses cmd ->
  let rec fold vs = function
    | [] ->
      (* parallel let: only bind at the end *)
      List.fold_left (fun cmd v -> Runtime.add_bound v cmd) cmd vs
    | Rsyntax.Let_clause_ML (_, _, c) :: clauses ->
      infer c >>= fun v ->
      fold (v :: vs) clauses
    | Rsyntax.Let_clause_patt (xs, pt, c) :: clauses ->
       infer c >>= fun v ->
       Matching.match_pattern pt v >>= begin function
        | Some us -> fold (List.rev us @ vs) clauses
        | None ->
           Runtime.lookup_penv >>= fun penv ->
           Runtime.(error ~loc (MatchFail v))
       end


  in
  fold [] clauses

and letrec_bind : 'a. _ -> 'a Runtime.comp -> 'a Runtime.comp = fun fxcs ->
  let gs =
    List.map
      (fun (_, _, _, c) -> (fun v -> Runtime.add_bound v (infer c)))
      fxcs
  in
  Runtime.add_bound_rec gs

(* [match_cases loc cases eval v] tries for each case in [cases] to match [v]
   and if successful continues on the computation using [eval] with the pattern variables bound. *)
and match_cases : type a. loc:_ -> _ -> (Rsyntax.comp -> a Runtime.comp) -> _ -> a Runtime.comp
 = fun ~loc cases eval v ->
  let rec fold = function
    | [] ->
      Runtime.lookup_penv >>= fun penv ->
      Runtime.(error ~loc (MatchFail v))
    | (_, p, c) :: cases ->
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

and check_is_type c : Jdg.is_type Runtime.comp =
  infer c >>= as_is_type ~loc:(c.Location.loc)

and check_is_term c =
  infer c >>= as_is_term ~loc:c.Location.loc

and check_eq_type c =
  infer c >>= as_eq_type ~loc:c.Location.loc

and check_eq_term c =
  infer c >>= as_eq_term ~loc:c.Location.loc

and check_atom c =
  infer c >>= as_atom ~loc:c.Location.loc

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
    | Rsyntax.Let_clause_ML (x, _, c) :: clauses ->
       comp_value c >>= fun v ->
       fold (v :: vs) clauses

    | Rsyntax.Let_clause_patt (_, pt, c) :: clauses ->
       comp_value c >>= fun v ->
       Matching.top_match_pattern pt v >>= begin function
        | None -> Runtime.error ~loc (Runtime.MatchFail v)
        | Some us -> fold (List.rev us @ vs) clauses
       end
  in
  fold [] clauses >>= fun () ->
    if not quiet then
      (List.iter (function
       | Rsyntax.Let_clause_ML (x, annot, _) ->
           Format.printf "@[<hov 2>val %t :>@ %t@]@."
                         (Name.print_ident x)
                         (print_annot annot)
       | Rsyntax.Let_clause_patt (xts, _, _) ->
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
      (fun (_, _, _, c) -> (fun v -> Runtime.add_bound v (infer c)))
      fxcs
  in
  Runtime.add_topbound_rec gs >>= fun () ->
  if not quiet then
    (List.iter
      (fun (f, _, annot, _) -> Format.printf "@[<hov 2>val %t :>@ %t@]@."
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
  Runtime.catch (lazy (match c with

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

    | Rsyntax.DeclConstants (xs, c) ->
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

  | Runtime.Value v -> return v
