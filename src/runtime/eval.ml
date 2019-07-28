(** Evaluation of computations *)

(** Notation for the monadic bind *)
let (>>=) = Runtime.bind

let return = Runtime.return

(** Conversion of runtime values to more specific values *)
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

let as_handler ~loc v =
  let e = Runtime.as_handler ~loc v in
  return e

let as_ref ~loc v =
  let e = Runtime.as_ref ~loc v in
  return e

let as_dyn ~loc v =
  let e = Runtime.as_dyn ~loc v in
  return e

(** Main evaluation loop. *)

(** Evaluate a computation. *)
let rec comp {Location.thing=c'; loc} =
  match c' with
    | Rsyntax.Bound i ->
       Runtime.lookup_bound i

    | Rsyntax.Value pth ->
       Runtime.lookup_ml_value pth

    | Rsyntax.Function c ->
       let f v =
         Runtime.add_bound v
           (comp c)
       in
       Runtime.return_closure f

    | Rsyntax.MLConstructor (t, cs) ->
       let rec fold vs = function
         | [] ->
            let vs = List.rev vs in
            return vs
         | c :: cs ->
            comp c >>= fun v ->
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
        | c :: cs -> (comp c >>= fun v -> fold (v :: vs) cs)
      in
      fold [] cs

    | Rsyntax.Handler {Rsyntax.handler_val; handler_ops; handler_finally} ->
        let handler_val =
          begin match handler_val with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~loc handler_val comp v
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
              match_cases ~loc handler_finally comp v
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
          comp c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Rsyntax.With (c1, c2) ->
     comp c1 >>= as_handler ~loc >>= fun h ->
     Runtime.handle_comp h (comp c2)

  | Rsyntax.Let (xcs, c) ->
     let_bind ~loc xcs (comp c)

  | Rsyntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (comp c)

  | Rsyntax.Now (x,c1,c2) ->
     let xloc = x.Location.loc in
     comp x >>= as_dyn ~loc:xloc >>= fun x ->
     comp c1 >>= fun v ->
     Runtime.now x v (comp c2)

  | Rsyntax.Current c ->
     comp c >>= as_dyn ~loc:(c.Location.loc) >>= fun x ->
     Runtime.lookup_dyn x

  | Rsyntax.Ref c ->
     comp c >>= fun v ->
     Runtime.mk_ref v

  | Rsyntax.Lookup c ->
     comp c >>= as_ref ~loc >>= fun x ->
     Runtime.lookup_ref x

  | Rsyntax.Update (c1, c2) ->
     comp c1 >>= as_ref ~loc >>= fun x ->
     comp c2 >>= fun v ->
     Runtime.update_ref x v >>= fun () ->
     Runtime.return_unit

  | Rsyntax.Sequence (c1, c2) ->
     comp c1 >>= fun v ->
     sequence ~loc v >>= fun () ->
     comp c2

  | Rsyntax.Assume ((None, c1), c2) ->
     comp_as_is_type c1 >>= fun _ ->
     comp c2

  | Rsyntax.Assume ((Some x, c1), c2) ->
     comp_as_is_type c1 >>= fun t ->
     Runtime.add_free x t (fun _ -> comp c2)

  | Rsyntax.Match (c, cases) ->
     comp c >>=
     match_cases ~loc cases comp

  | Rsyntax.BoundaryAscribe (c1, c2) ->
     comp_as_boundary_abstraction c2 >>= fun bdry ->
     check_judgement c1 bdry >>=
     Runtime.return_judgement

  | Rsyntax.Abstract (x, None, _) ->
    Runtime.(error ~loc (UnannotatedAbstract x))

  | Rsyntax.Abstract (x, Some u, c) ->
     comp_as_is_type u >>= fun u ->
     Runtime.add_free x u
       (fun a ->
         Reflect.add_abstracting
           (Nucleus.form_is_term_atom a)
           begin comp c >>=
             function
             | Runtime.Judgement jdg -> Runtime.return_judgement (Nucleus.abstract_judgement a jdg)

             | Runtime.Boundary bdry -> Runtime.return_boundary (Nucleus.abstract_boundary a bdry)

             | Runtime.(Closure _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as v ->
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
     comp_as_judgement_abstraction c1 >>= fun abstr ->
     begin match Nucleus.type_at_abstraction abstr with
       | None -> Runtime.(error ~loc AbstractionExpected)
       | Some t ->
          check_judgement c2 (Nucleus.abstract_not_abstract (Nucleus.form_is_term_boundary t)) >>= fun jdg ->
          begin match Nucleus.as_not_abstract jdg with
          | Some (Nucleus.JudgementIsTerm e) ->
               Runtime.lookup_signature >>= fun sgn ->
               let abstr = Nucleus.apply_judgement_abstraction sgn abstr e in
               Runtime.return_judgement abstr
          | None
          | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
             Runtime.(error ~loc (IsTermExpected (Runtime.Judgement jdg)))
          end
     end

  | Rsyntax.Yield c ->
    comp c >>= fun v ->
    Runtime.continue v

  | Rsyntax.Apply (c1, c2) ->
    comp c1 >>= begin function
      | Runtime.Closure f ->
        comp c2 >>= fun v ->
        Runtime.apply_closure f v
      | Runtime.(Judgement _ | Boundary _ | Handler _ | Tag _ | Tuple _ | Ref _ | Dyn _ | String _) as h ->
        Runtime.(error ~loc (Inapplicable h))
    end

  | Rsyntax.String s ->
    return (Runtime.mk_string s)

  | Rsyntax.Occurs (c1, c2) ->
     comp_as_atom c1 >>= fun a ->
     comp_as_judgement_abstraction c2 >>= fun abstr ->
     begin match Nucleus.occurs_judgement_abstraction a abstr with
     | true ->
        let t = Runtime.Judgement (Nucleus.(abstract_not_abstract (JudgementIsType (type_of_atom a)))) in
        return (Reflect.mk_option (Some t))
     | false ->
        return (Reflect.mk_option None)
     end

  | Rsyntax.Convert (c1, c2) ->
     comp_as_judgement_abstraction c1 >>= fun jdg ->
     comp_as_eq_type_abstraction c2 >>= fun eq ->
     Runtime.get_env >>= fun env ->
     let sgn = Runtime.get_signature env in
     begin match Nucleus.convert_judgement_abstraction sgn jdg eq with
     | None -> Runtime.(error ~loc (InvalidConvert (jdg, eq)))
     | Some jdg -> Runtime.return_judgement jdg
     end

  | Rsyntax.Context c ->
    comp_as_is_term_abstraction c >>= fun abstr ->
    let xts = Nucleus.context_is_term_abstraction abstr in
    let js =
      List.map
        (fun atm -> Runtime.Judgement Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom atm))))
        xts
    in
    return (Reflect.mk_list js)

  | Rsyntax.Natural c ->
    comp_as_is_term c >>= fun jdg_e ->
    Runtime.lookup_signature >>= fun signature ->
    let eq = Nucleus.natural_type_eq signature jdg_e in
    Runtime.return_judgement Nucleus.(abstract_not_abstract (JudgementEqType eq))

  | Rsyntax.MLBoundary bdry ->
     eval_boundary ~loc bdry >>= fun bdry ->
     Runtime.return_boundary Nucleus.(abstract_not_abstract bdry)

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
     assert false (* cannot happen, desugaring prevents this by checking arities of constructors *)
  | Nucleus.RapMore _, [] ->
     assert false (* cannot happen, desugaring prevetns this by checking arities of constructors  *)

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
and check_judgement ({Location.thing=c';loc} as c) bdry =
  match c' with

  (* These have no use for the boundary, so we just try to coerce them after they are evaluated *)
  | Rsyntax.Bound _
  | Rsyntax.Value _
  | Rsyntax.Function _
  | Rsyntax.Handler _
  | Rsyntax.BoundaryAscribe _
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
  | Rsyntax.Convert _
  | Rsyntax.Substitute _
  | Rsyntax.Context _
  | Rsyntax.Natural _
  | Rsyntax.MLBoundary _
    ->

    comp c >>= fun v ->
    coerce ~loc v bdry

  | Rsyntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op ~checking:bdry vs >>= fun v ->
          coerce ~loc v bdry
       | c :: cs ->
          comp c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Rsyntax.Let (xcs, c) ->
     let_bind ~loc xcs (check_judgement c bdry)

  | Rsyntax.Sequence (c1,c2) ->
    comp c1 >>= fun v ->
    sequence ~loc v >>= fun () ->
    check_judgement c2 bdry

  | Rsyntax.LetRec (fxcs, c) ->
     letrec_bind fxcs (check_judgement c bdry)

  | Rsyntax.Now (x,c1,c2) ->
     let xloc = x.Location.loc in
     comp x >>= as_dyn ~loc:xloc >>= fun x ->
     comp c1 >>= fun v ->
     Runtime.now x v (check_judgement c2 bdry)

  | Rsyntax.Assume ((Some x, t), c) ->
     comp_as_is_type t >>= fun t ->
     Runtime.add_free x t (fun _ ->
     check_judgement c bdry)

  | Rsyntax.Assume ((None, t), c) ->
     comp_as_is_type t >>= fun _ ->
     check_judgement c bdry

  | Rsyntax.Match (c, cases) ->
     comp c >>=
     match_cases ~loc cases (fun c -> check_judgement c bdry)

  | Rsyntax.Abstract (xopt, uopt, c) ->
    check_abstract ~loc bdry xopt uopt c

(** Run the abstraction [Abstract(x, uopt, c)] and check it against the boundary abstraction [bdry]. *)
and check_abstract ~loc bdry x uopt c =
  match Nucleus.invert_boundary_abstraction bdry with

  | Nucleus.Stump_NotAbstract _ ->
     Runtime.(error ~loc AbstractionExpected)

  | Nucleus.Stump_Abstract (a, bdry) ->
     (* NB: [a] is a fresh atom at this point. *)
     begin match uopt with

     | None ->
        Runtime.add_bound
          (Runtime.Judgement Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom a))))
          begin
            check_judgement c bdry >>= fun jdg ->
            let jdg = Nucleus.abstract_judgement a jdg in
            return jdg
          end

     | Some ({Location.loc=u_loc;_} as u) ->
        comp_as_is_type u >>= fun u ->
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
                 check_judgement c bdry >>= fun jdg ->
                 let jdg = Nucleus.abstract_judgement a jdg in
                 return jdg
               end
          end
     end

and sequence ~loc v =
  match v with
    | Runtime.Tuple [] -> return ()
    | _ ->
      Print.warning "@[<hov 2>%t: this value should be the unit (and why is this a runtime warning?) @]@."
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
       comp c >>= fun v ->
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
      (fun (Rsyntax.Letrec_clause c) -> (fun v -> Runtime.add_bound v (comp c)))
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
                  comp_as_bool g >>= function
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
        | Some vs -> List.fold_left (fun cmp v -> Runtime.add_bound v cmp) (comp c) vs
        | None -> fold cases
      end
  in
  fold cases

(** Run [c] and convert the result to an type judgement. *)
and comp_as_is_type c =
  comp c >>= fun v -> return (Runtime.as_is_type ~loc:c.Location.loc v)

(** Run [c] and convert the result to an term judgement. *)
and comp_as_is_term c =
  comp c >>= fun v -> return (Runtime.as_is_term ~loc:c.Location.loc v)

(** Run [c] and convert the result to a term abstraction. *)
and comp_as_is_term_abstraction c =
  comp c >>= fun v -> return (Runtime.as_is_term_abstraction ~loc:c.Location.loc v)

(** Run [c] and convert the result to a judgement abstraction. *)
and comp_as_judgement_abstraction c =
  comp c >>= fun v ->
  return (Runtime.as_judgement_abstraction ~loc:c.Location.loc v)

(** Run [c] and convert the result to a boundary abstraction. *)
and comp_as_boundary_abstraction c =
  comp c >>= fun v -> return (Runtime.as_boundary_abstraction ~loc:c.Location.loc v)

(** Run [c] and convert the result to a boundary abstraction. *)
and comp_as_eq_type_abstraction c =
  comp c >>= fun v -> return (Runtime.as_eq_type_abstraction ~loc:c.Location.loc v)

and comp_as_atom c =
  comp c >>= fun v -> (as_atom ~loc:c.Location.loc v)

(** Run [c] and convert it to a boolean. *)
and comp_as_bool c =
  comp c >>= fun v -> (as_bool ~loc:c.Location.loc v)

and eval_boundary ~loc = function
  | Rsyntax.BoundaryIsType ->
     Runtime.return Nucleus.(form_is_type_boundary)

  | Rsyntax.BoundaryIsTerm c ->
     comp_as_is_type c >>= fun t ->
     Runtime.return Nucleus.(form_is_term_boundary t)

  | Rsyntax.BoundaryEqType (c1, c2) ->
     comp_as_is_type c1 >>= fun t1 ->
     comp_as_is_type c2 >>= fun t2 ->
     Runtime.return Nucleus.(form_eq_type_boundary t1 t2)

  | Rsyntax.BoundaryEqTerm (c1, c2, c3) ->
     comp_as_is_type c3 >>= fun t ->
     Runtime.get_env >>= fun env ->
     let sgn = Runtime.get_signature env in
     let bdry = Nucleus.(abstract_not_abstract (form_is_term_boundary t)) in
     check_judgement c1 bdry >>= fun e1 ->
     let e1 =
       match Nucleus.as_is_term (Runtime.as_not_abstract ~loc e1) with
       | Some e1 -> e1
       | None -> assert false
     in
     check_judgement c2 bdry >>= fun e2 ->
     let e2 =
       match Nucleus.as_is_term (Runtime.as_not_abstract ~loc e2) with
       | Some e2 -> e2
       | None -> assert false
     in
     Runtime.return Nucleus.(form_eq_term_boundary sgn e1 e2)

(** Move to toplevel monad *)

let comp_value c =
  let r = comp c in
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
       comp_as_is_type c >>= fun t ->
       Runtime.add_free x t
         (fun a ->
            Reflect.add_abstracting
              (Nucleus.form_is_term_atom a)
              (fold lctx >>= fun abstr ->
               return (Nucleus.abstract_boundary a abstr)
         ))
  in
  fold lctx

let premise {Location.thing=Rsyntax.Premise(x, lctx, bdry); loc} =
  local_context lctx (eval_boundary ~loc bdry) >>= fun bdry ->
  Runtime.lookup_signature >>= fun sgn ->
  let mv = Nucleus.fresh_judgement_meta x bdry in
  let v = Runtime.Judgement (Nucleus.judgement_meta_eta_expanded sgn mv) in
  return ((Nucleus.meta_nonce mv, bdry), v)


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
       premise prem >>= fun (x_boundary, v) ->
       let cmp = fold (x_boundary :: prems_out) prems in
       Runtime.add_bound v cmp
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
      (fun (Rsyntax.Letrec_clause c) v -> Runtime.add_bound v (comp c))
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
     Runtime.top_handle ~loc (premises prems (eval_boundary ~loc bdry)) >>= fun (premises, head) ->
     let rule = Nucleus.form_rule premises head in
     (if not quiet then
        Format.printf "@[<hov 2>Rule %t is postulated.@]@." (Ident.print ~opens ~parentheses:false x));
     Runtime.add_rule x rule

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
