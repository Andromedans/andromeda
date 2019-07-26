(** Evaluation of computations *)

(** Notation for the monadic bind *)
let (>>=) = Runtime.bind

let return = Runtime.return

let as_atom ~loc v =
  Runtime.lookup_signature >>= fun sgn ->
  let j = Runtime.as_is_term ~loc v in
  match Nucleus.invert_is_term sgn j with
    | Nucleus.Stump_TermAtom x -> return x
    | Nucleus.(Stump_TermConstructor _ | Stump_TermMeta _ | Stump_TermConvert _) ->
       Runtime.(error ~loc (ExpectedAtom j))

let mlfalse, _, _ = Typecheck.Builtin.mlfalse
let mltrue, _, _ = Typecheck.Builtin.mltrue

let as_bool ~loc v =
  match v with
  | Runtime.Tag (l, []) ->
     if Runtime.equal_tag l mlfalse then
       return false
     else if Runtime.equal_tag l mltrue then
       return true
     else
     Runtime.(error ~loc (BoolExpected v))

  | Runtime.(Tag (_, _::_) | Judgement _ | Boundary _ | Closure _ | Handler _ | Tuple _ | Ref _ | Dyn _ | String _) ->
     Runtime.(error ~loc (BoolExpected v))


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
  match c' with
    | Rsyntax.Bound i ->
       Runtime.lookup_bound i

    | Rsyntax.Value pth ->
       Runtime.lookup_ml_value pth

    | Rsyntax.Function c ->
       let f v =
         Runtime.add_bound v
           (infer c)
       in
       Runtime.return_closure f

    | Rsyntax.MLConstructor (t, cs) ->
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

    | Rsyntax.TTConstructor (c, cs) ->
       Runtime.lookup_signature >>= fun sgn ->
       let rap = Nucleus.form_rap sgn c in
       check_arguments rap cs

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
        and handler_ops = Ident.mapi (fun op cases ->
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

  | Rsyntax.Assume ((None, c1), c2) ->
     infer_is_type c1 >>= fun _ ->
     infer c2

  | Rsyntax.Assume ((Some x, c1), c2) ->
     infer_is_type c1 >>= fun t ->
     Runtime.add_free x t (fun _ -> infer c2)

  | Rsyntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases infer

  | Rsyntax.Ascribe (c1, c2) ->
     infer_boundary_abstraction c2 >>= fun bdry ->
     check_judgement c1 bdry >>=
     Runtime.return_judgement

  | Rsyntax.Abstract (x, None, _) ->
    Runtime.(error ~loc (UnannotatedAbstract x))

  | Rsyntax.Abstract (x, Some u, c) ->
     infer_is_type u >>= fun u ->
     Runtime.add_free x u
       (fun a ->
         Reflect.add_abstracting
           (Nucleus.form_is_term_atom a)
           begin infer c >>=
             function
             | Runtime.Judgement jdg -> Runtime.return_judgement (Nucleus.abstract_judgement a jdg)

             | Runtime.(Boundary _ | Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
                Runtime.(error ~loc (JudgementExpected v))

           end)

  | Rsyntax.Substitute (c1, c2) ->
     (*

        Checking is kind of useless:

        c1  ==>  {x:A} jdg     c2  <==  A --> s   jdg[s/x] = C
        ------------------------------------------------------
            c1{c2}  <== C


        Abstractions want to be inferred, like applications.

        * c1 has to be an abstraction (not very useful)
        * either
          + c1  ==>  {x:A} jdg
          + c2  <==  A --> s
        * or
          + c2  ==>  A
          + c1  <==  {x:A} α     for α fresh.
            Mlty doesn't currently allow us to do this because we need to know
            what judgement we're abstracting over.
        ---------------------------------
            c1{c2}  ==>  jdg[s/x]

 *)
     infer_judgement_abstraction c1 >>= fun abstr ->
     begin match Nucleus.type_at_abstraction abstr with
       | None -> Runtime.(error ~loc (JudgementAbstractionExpected (Runtime.Judgement abstr)))
       | Some t ->
          check_judgement c2 (Nucleus.abstract_not_abstract (Nucleus.BoundaryIsTerm t)) >>= fun abstr ->
          begin match Nucleus.as_not_abstract abstr with
          | Some (Nucleus.JudgementIsTerm e) ->
               Runtime.lookup_signature >>= fun sgn ->
               let abstr = Nucleus.apply_judgement_abstraction sgn abstr e in
               Runtime.return_judgement abstr
          | None
          | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
             Runtime.(error ~loc (IsTermExpected (Runtime.Judgement abstr)))
          end
     end

  | Rsyntax.Yield c ->
    infer c >>= fun v ->
    Runtime.continue v

  | Rsyntax.Apply (c1, c2) ->
    infer c1 >>= begin function
      | Runtime.Closure f ->
        infer c2 >>= fun v ->
        Runtime.apply_closure f v
      | Runtime.(Judgement _ | Boundary _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as h ->
        Runtime.(error ~loc (Inapplicable h))
    end

  | Rsyntax.String s ->
    return (Runtime.mk_string s)

  | Rsyntax.Occurs (c1,c2) ->
     infer_atom c1 >>= fun a ->
     infer_judgement_abstraction c2 >>= fun abstr ->
     begin match Nucleus.occurs_judgement_abstraction a abstr with
     | true ->
        let t = Runtime.Judgement (Nucleus.(abstract_not_abstract (JudgementIsType (type_of_atom a)))) in
        return (Reflect.mk_option (Some t))
     | false ->
        return (Reflect.mk_option None)
     end

  | Rsyntax.Context c ->
    infer_is_term_abstraction c >>= fun abstr ->
    let xts = Nucleus.context_is_term_abstraction abstr in
    let js =
      List.map
        (fun atm -> Runtime.Judgement Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom atm))))
        xts
    in
    return (Reflect.mk_list js)

  | Rsyntax.Natural c ->
    infer_is_term c >>= fun jdg_e ->
    Runtime.lookup_signature >>= fun signature ->
    let eq = Nucleus.natural_type_eq signature jdg_e in
    Runtime.return_judgement Nucleus.(abstract_not_abstract (JudgementEqType eq))

and check_arguments rap cs =
  match rap, cs with
  | Nucleus.RapDone jdg, [] -> Runtime.return_judgement (Nucleus.abstract_not_abstract jdg)
  | Nucleus.RapMore rap, c :: cs ->
     let bdry = Nucleus.rap_boundary rap in
     Runtime.lookup_signature >>= fun sgn ->
     check_judgement c bdry >>= fun arg ->
     let rap = Nucleus.rap_apply sgn rap arg in
     check_arguments rap cs
  | Nucleus.RapDone _, _::_ ->
     assert false (* cannot happen, typechecking prevents this *)
  | Nucleus.RapMore _, [] ->
     assert false (* cannot happen, typechecking prevents this *)


(** Coerce the value [v] to the given judgement boundary [bdry] *)
and coerce ~loc v (bdry : Nucleus.boundary_abstraction) =
  let abstr = Runtime.as_judgement_abstraction ~loc v in
  Runtime.lookup_signature >>= fun sgn ->
  Equal.coerce ~loc sgn abstr bdry >>=
    begin function
      | None -> Runtime.(error ~loc (TypeMismatchCheckingMode (abstr, bdry)))
      | Some e -> return e
    end

(** Compute a judgement with the given abstracted boundary *)
and check_judgement ({Location.thing=c';loc} as c) (bdry : Nucleus.boundary_abstraction) : Nucleus.judgement_abstraction Runtime.comp =
  match c' with

  (* for these we switch to infer mode *)
  | Rsyntax.Bound _
  | Rsyntax.Value _
  | Rsyntax.Function _
  | Rsyntax.Handler _
  | Rsyntax.Ascribe _
  | Rsyntax.MLConstructor _
  | Rsyntax.TTConstructor _
  | Rsyntax.Tuple _
  | Rsyntax.With _
  | Rsyntax.Yield _
  | Rsyntax.Apply _
  | Rsyntax.Ref _
  | Rsyntax.Lookup _
  | Rsyntax.Update _
  | Rsyntax.Current _
  | Rsyntax.String _
  | Rsyntax.Occurs _
  | Rsyntax.Substitute _
  | Rsyntax.Context _
  | Rsyntax.Natural _ ->

    infer c >>= fun v ->
    coerce ~loc v bdry

  | Rsyntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op ~checking:bdry vs >>= fun v ->
          coerce ~loc v bdry
       | c :: cs ->
          infer c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Rsyntax.Let (xcs, c) ->
     let_bind ~loc xcs (check_judgement c bdry)

  | Rsyntax.Sequence (c1,c2) ->
    infer c1 >>= fun v ->
    sequence ~loc v >>= fun () ->
    check_judgement c2 bdry

  | Rsyntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (check_judgement c bdry)

  | Rsyntax.Now (x,c1,c2) ->
     let xloc = x.Location.loc in
     infer x >>= as_dyn ~loc:xloc >>= fun x ->
     infer c1 >>= fun v ->
     Runtime.now x v (check_judgement c2 bdry)

  | Rsyntax.Assume ((Some x, t), c) ->
     infer_is_type t >>= fun t ->
     Runtime.add_free x t (fun _ ->
     check_judgement c bdry)

  | Rsyntax.Assume ((None, t), c) ->
     infer_is_type t >>= fun _ ->
     check_judgement c bdry

  | Rsyntax.Match (c, cases) ->
     infer c >>=
     match_cases ~loc cases (fun c -> check_judgement c bdry)

  | Rsyntax.Abstract (xopt, uopt, c) ->
    check_abstract ~loc bdry xopt uopt c

(** Run the abstraction [Abstract(x, uopt, c)] in checking mode with boundary abstraction [bdry]. *)
and check_abstract ~loc bdry x uopt c =
  match Nucleus.as_abstract bdry with

  | None ->
     Runtime.(error ~loc (UnexpectedAbstraction bdry))

  | Some (a, bdry) ->
     (* NB: [a] is a fresh atom at this point. *)
     begin match uopt with

     | None ->
        Runtime.add_bound
          (Runtime.Judgement Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom a))))
          begin
            check_judgement c bdry
          end

     | Some ({Location.loc=u_loc;_} as u) ->
        infer_is_type u >>= fun u ->
        let a_type = Nucleus.type_of_atom a in
        Equal.equal_type ~loc:u_loc a_type u >>=
          begin function
            | None ->
               Runtime.(error ~loc:u_loc (TypeEqualityFail (u, a_type)))
            | Some eq (* : a_type == u *) ->
               Runtime.lookup_signature >>= fun sgn ->
               let a' =
                 Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_convert sgn (form_is_term_atom a) eq)))
               in
               Runtime.add_bound
               (Runtime.Judgement a')
               begin
                 check_judgement c bdry
               end
          end
     end

and sequence ~loc v =
  match v with
    | Runtime.Tuple [] -> return ()
    | _ ->
      Print.warning "@[<hov 2>%t: this value should be the unit@]@."
        (Location.print loc) ;
      return ()

and let_bind
  : 'a. loc:Location.t -> Rsyntax.let_clause list -> 'a Runtime.comp -> 'a Runtime.comp
  = fun ~loc clauses cmp ->
  let rec fold uss = function
    | [] ->
      (* parallel let: only bind at the end *)
      (* suppose we had the following parallel let:

            let (x, y, z) = (a, b, c)
            and (u, v)    = (1, 2)

        then uss will be [[2;1]; [c; b; a]].
        Here v has de Bruijn index 0 and x has de Bruijn index 4. *)
       List.fold_left
         (List.fold_left (fun cmp u -> Runtime.add_bound u cmp))
         cmp uss
    | Rsyntax.Let_clause (pt, c) :: clauses ->
       infer c >>= fun v ->
       Matching.match_pattern pt v >>= begin function
        | Some us -> fold (us :: uss) clauses
        | None -> Runtime.(error ~loc (MatchFail v))
       end

  in
  fold [] clauses

and letrec_bind
  : 'a . Rsyntax.letrec_clause list -> 'a Runtime.comp -> 'a Runtime.comp
  = fun fxcs ->
  let gs =
    List.map
      (fun (Rsyntax.Letrec_clause c) -> (fun v -> Runtime.add_bound v (infer c)))
      fxcs
  in
  Runtime.add_bound_rec gs

(* [match_cases loc cases eval v] tries for each case in [cases] to match [v] and if
   successful continues on the computation using [eval] with the pattern variables bound.
   *)
and match_cases
  : 'a . loc:Location.t -> Rsyntax.match_case list -> (Rsyntax.comp -> 'a Runtime.comp)
         -> Runtime.value -> 'a Runtime.comp
  = fun ~loc cases eval v ->
  let bind_pattern_vars vs cmp =
    List.fold_left (fun cmp v -> Runtime.add_bound v cmp) cmp vs
  in
  let rec fold = function
    | [] -> Runtime.(error ~loc (MatchFail v))
    | (p, g, c) :: cases ->
      Matching.match_pattern p v >>= begin function
        | None -> fold cases
        | Some vs ->
           begin
             match g with
             | None -> bind_pattern_vars vs (eval c)
             | Some g ->
                Runtime.get_env >>= fun env ->
                bind_pattern_vars vs
                begin
                  check_bool g >>= function
                  | false -> Runtime.with_env env (fold cases)
                  | true -> eval c
                end
           end
      end
  in
  fold cases

and match_op_cases ~loc op cases vs checking =
  let rec fold = function
    | [] ->
      Runtime.operation op ?checking vs >>= fun v ->
      Runtime.continue v
    | (ps, ptopt, c) :: cases ->
      Matching.match_op_pattern ~loc ps ptopt vs checking >>=
        begin function
        | Some vs -> List.fold_left (fun cmp v -> Runtime.add_bound v cmp) (infer c) vs
        | None -> fold cases
      end
  in
  fold cases

(** Run [c] in infer mode and convert the result to an type judgement. *)
and infer_is_type c =
  infer c >>= fun v -> return (Runtime.as_is_type ~loc:c.Location.loc v)

(** Run [c] in infer mode and convert the result to a type abstraction. *)
(* and infer_is_type_abstraction c = *)
(*   infer c >>= fun v -> return (Runtime.as_is_type_abstraction ~loc:c.Location.loc v) *)

(** Run [c] in infer mode and convert the result to an term judgement. *)
and infer_is_term c =
  infer c >>= fun v -> return (Runtime.as_is_term ~loc:c.Location.loc v)

(** Run [c] in infer mode and convert the result to a term abstraction. *)
and infer_is_term_abstraction c =
  infer c >>= fun v -> return (Runtime.as_is_term_abstraction ~loc:c.Location.loc v)

(** Run [c] in infer mode and convert the result to a type equality abstraction. *)
(* and infer_eq_type_abstraction c = *)
(*   infer c >>= fun v -> return (Runtime.as_eq_type_abstraction ~loc:c.Location.loc v) *)

(** Run [c] in infer mode and convert the result to a term equality abstraction. *)
(* and infer_eq_term_abstraction c = *)
(*   infer c >>= fun v -> return (Runtime.as_eq_term_abstraction ~loc:c.Location.loc v) *)

(** Run [c] in infer mode and convert the result to a judgement abstraction. *)
and infer_judgement_abstraction c =
  infer c >>= fun v -> return (Runtime.as_judgement_abstraction ~loc:c.Location.loc v)

(** Run [c] in infer mode and convert the result to a boundary abstraction. *)
and infer_boundary_abstraction c =
  infer c >>= fun v -> return (Runtime.as_boundary_abstraction ~loc:c.Location.loc v)

and infer_atom c =
  infer c >>= fun v -> (as_atom ~loc:c.Location.loc v)

(** Run [c] and convert it to a boolean. *)
and check_bool c =
  infer c >>= fun v -> (as_bool ~loc:c.Location.loc v)

(** Move to toplevel monad *)

let comp_value c =
  let r = infer c in
  Runtime.top_handle ~loc:c.Location.loc r

(** Evaluation of rules *)

(* Evaluate the computation [cmp] in local context [lctx].
   Return the evaluated [lctx] and the result of [cmp]. *)
let local_context lctx cmp =
  let rec fold = function
    | [] ->
       cmp >>= fun v ->
       return (Nucleus.abstract_not_abstract v)
    | (x, c) :: lctx ->
       infer_is_type c >>= fun t ->
       Runtime.add_free x t
         (fun a ->
            Reflect.add_abstracting
              (Nucleus.form_is_term_atom a)
              (fold lctx >>= fun abstr ->
               return (Nucleus.abstract_boundary a abstr)
         ))
  in
  fold lctx

let check_eq_type_boundary (c1, c2) =
  infer_is_type c1 >>= fun t1 ->
  infer_is_type c2 >>= fun t2 ->
  return (t1, t2)

(* Run [c] in checking mode, making sure it's a term judgement of type [t] *)
let check_is_term c t =
  let bdry = Nucleus.(abstract_not_abstract (BoundaryIsTerm t)) in
  check_judgement c bdry >>= fun abstr ->
  match Nucleus.as_not_abstract abstr with
  | Some (Nucleus.JudgementIsTerm e) -> return e
  | None
  | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
     assert false

let check_eq_term_boundary (c1, c2, c3) =
  infer_is_type c3 >>= fun t ->
  check_is_term c1 t >>= fun e1 ->
  check_is_term c2 t >>= fun e2 ->
  return (e1, e2, t)

let eval_boundary = function
  | Rsyntax.BoundaryIsType ->
     return (Nucleus.BoundaryIsType ())

  | Rsyntax.BoundaryIsTerm c ->
     infer_is_type c >>= fun t ->
     return (Nucleus.BoundaryIsTerm t)

  | Rsyntax.BoundaryEqType (c1, c2) ->
     check_eq_type_boundary (c1, c2) >>= fun (t1, t2) ->
     return (Nucleus.BoundaryEqType (t1, t2))

  | Rsyntax.BoundaryEqTerm (c1, c2, c3) ->
     check_eq_term_boundary (c1, c2, c3) >>= fun (e1, e2, t) ->
     return (Nucleus.BoundaryEqTerm (e1, e2, t))

let premise {Location.thing=Rsyntax.Premise(xopt, lctx, bdry);_} =
  local_context lctx (eval_boundary bdry) >>= fun bdry ->
  Runtime.lookup_signature >>= fun sgn ->
  let x = (match xopt with Some x -> x | None -> Name.anonymous ()) in
  let mv = Nucleus.fresh_meta x bdry in
  let v = Runtime.Judgement (Nucleus.meta_eta_expanded sgn mv) in
  return ((Nucleus.meta_nonce mv, bdry), Some v)


(** Evaluate the premises (should we call them arguments?) of a rule,
    bind them to meta-variables, then evaluate the conclusion [cmp].
    Return the evaulated premises and conclusion for further processing.
*)
let premises prems cmp =
  let rec fold prems_out = function

    | [] ->
       cmp >>= fun v ->
       let prems_out = List.rev prems_out in
       return (prems_out, v)

    | prem :: prems ->
       premise prem >>= fun (x_boundary, vopt) ->
       let cmp = fold (x_boundary :: prems_out) prems in
       match vopt with
       | None -> cmp
       | Some v -> Runtime.add_bound v cmp
  in
  fold [] prems


(** Toplevel commands *)

let (>>=) = Runtime.top_bind
let return = Runtime.top_return

let toplet_bind ~loc ~quiet ~print_annot info clauses =
  let rec fold uss = function
    | [] ->
       (* parallel let: only bind at the end *)
       List.fold_left
         (List.fold_left (fun cmp u -> Runtime.add_ml_value u >>= fun () -> cmp))
         (return uss)
         uss

    | Rsyntax.Let_clause (pt, c) :: clauses ->
       comp_value c >>= fun v ->
       Matching.top_match_pattern pt v >>= begin function
        | None -> Runtime.error ~loc (Runtime.MatchFail v)
        | Some us -> fold (us :: uss) clauses
       end
  in
  fold [] clauses >>= fun uss ->
  Runtime.top_lookup_penv >>= fun penv ->
    if not quiet
    then
      begin
        let vss = List.rev (List.map List.rev uss) in
        List.iter2
          (fun xts xvs ->
            List.iter2
              (fun (x, sch) v ->
                Format.printf "@[<hov 2>val %t :>@ %t@ =@ %t@]@."
                              (Name.print x)
                              (print_annot sch)
                              (Runtime.print_value ~penv v))
              xts xvs)
          info vss
       end ;
    return ()

let topletrec_bind ~loc ~quiet ~print_annot info fxcs =
  let gs =
    List.map
      (fun (Rsyntax.Letrec_clause c) v -> Runtime.add_bound v (infer c))
      fxcs
  in
  Runtime.add_ml_value_rec gs >>= fun () ->
  if not quiet then
    (List.iter
      (fun (f, annot) ->
        Format.printf "@[<hov 2>val %t :>@ %t@]@."
                      (Name.print f)
                      (print_annot annot))
      info) ;
  return ()

let rec toplevel ~quiet ~print_annot {Location.thing=c;loc} =
  match c with

  | Rsyntax.Rule (x, prems, bdry) ->
     Runtime.top_lookup_opens >>= fun opens ->
     Runtime.top_handle ~loc (premises prems (eval_boundary bdry)) >>= fun (premises, head) ->
     let rule = Nucleus.form_rule premises head in
     (if not quiet then
        Format.printf "@[<hov 2>Rule %t is postulated.@]@." (Ident.print ~opens ~parentheses:false x));
     Runtime.add_rule x rule

  (* | Rsyntax.RuleIsTerm (x, prems, c) -> *)
  (*    Runtime.top_lookup_opens >>= fun opens -> *)
  (*    Runtime.top_handle ~loc (premises prems (infer_is_type c)) >>= *)
  (*      fun (premises, head) -> *)
  (*      let rule = Nucleus.form_rule_is_term premises head in *)
  (*      (if not quiet then *)
  (*         Format.printf "@[<hov 2>Rule %t is postulated.@]@." (Ident.print ~opens ~parentheses:false x)); *)
  (*      Runtime.add_rule_is_term x rule *)

  (* | Rsyntax.RuleEqType (x, prems, boundary) -> *)
  (*    Runtime.top_lookup_opens >>= fun opens -> *)
  (*    Runtime.top_handle ~loc (premises prems (check_eq_type_boundary boundary)) >>= *)
  (*      fun (premises, head) -> *)
  (*      let rule = Nucleus.form_rule_eq_type premises head in *)
  (*      (if not quiet then *)
  (*         Format.printf "@[<hov 2>Rule %t is postulated.@]@." (Ident.print ~opens ~parentheses:false x)); *)
  (*      Runtime.add_rule_eq_type x rule *)

  (* | Rsyntax.RuleEqTerm (x, prems, boundary) -> *)
  (*    Runtime.top_lookup_opens >>= fun opens -> *)
  (*    Runtime.top_handle ~loc (premises prems (check_eq_term_boundary boundary)) >>= *)
  (*      fun (premises, head) -> *)
  (*      let rule = Nucleus.form_rule_eq_term premises head in *)
  (*      (if not quiet then *)
  (*         Format.printf "@[<hov 2>Rule %t is postulated.@]@." (Ident.print ~opens ~parentheses:false x)); *)
  (*      Runtime.add_rule_eq_term x rule *)

  | Rsyntax.DefMLType lst
  | Rsyntax.DefMLTypeRec lst ->
     Runtime.top_lookup_opens >>= fun opens ->
     (if not quiet then
        Format.printf "@[<hov 2>ML type%s %t declared.@]@."
          (match lst with [_] -> "" | _ -> "s")
          (Print.sequence (Path.print ~opens ~parentheses:true) "," lst)) ;
     return ()

  | Rsyntax.DeclOperation (op, k) ->
     Runtime.top_lookup_opens >>= fun opens ->
     (if not quiet then
        Format.printf "@[<hov 2>Operation %t is declared.@]@."
          (Path.print ~opens ~parentheses:true op)) ;
     return ()

  | Rsyntax.DeclExternal (x, sch, s) ->
     begin
       match External.lookup s with
       | None -> Runtime.error ~loc (Runtime.UnknownExternal s)
       | Some v ->
          Runtime.add_ml_value v >>= (fun () ->
           if not quiet then
             Format.printf "@[<hov 2>external %t :@ %t = \"%s\"@]@."
               (Name.print x)
               (print_annot () sch)
               s ;
           return ())
     end

  | Rsyntax.TopLet (info, clauses) ->
     let print_annot = print_annot () in
     toplet_bind ~loc ~quiet ~print_annot info clauses

  | Rsyntax.TopLetRec (info, fxcs) ->
     let print_annot = print_annot () in
     topletrec_bind ~loc ~quiet ~print_annot info fxcs

  | Rsyntax.TopComputation (c, sch) ->
     comp_value c >>= fun v ->
     Runtime.top_lookup_penv >>= fun penv ->
     if not quiet then
       Format.printf "@[<hov 2>- :@ %t@ =@ %t@]@."
           (print_annot () sch)
           (Runtime.print_value ~penv v) ;
     return ()

  | Rsyntax.TopDynamic (x, annot, c) ->
     comp_value c >>= fun v ->
     Runtime.add_dynamic x v

  | Rsyntax.TopNow (x,c) ->
     let xloc = x.Location.loc in
     comp_value x >>= fun x ->
     let x = Runtime.as_dyn ~loc:xloc x in
     comp_value c >>= fun v ->
     Runtime.top_now x v

  | Rsyntax.Open pth ->
     Runtime.top_open_path pth

  | Rsyntax.MLModule (mdl_name, cmds) ->
     if not quiet then Format.printf "@[<hov 2>Processing module %t@]@." (Name.print mdl_name) ;
     Runtime.as_ml_module (toplevels ~quiet ~print_annot cmds)

  | Rsyntax.Verbosity i -> Config.verbosity := i; return ()

and toplevels ~quiet ~print_annot =
  Runtime.top_fold
    (fun () -> toplevel ~quiet ~print_annot)
    ()
