(** Evaluation of computations *)

(** Notation for the monadic bind *)
let (>>=) = Runtime.bind

let return = Runtime.return

(** Conversion of runtime values to more specific values *)
let as_atom ~at v =
  Runtime.lookup_signature >>= fun sgn ->
  let j = Runtime.as_is_term ~at v in
  match Nucleus.invert_is_term sgn j with
    | Nucleus.Stump_TermAtom x -> return x
    | Nucleus.(Stump_TermConstructor _ | Stump_TermMeta _ | Stump_TermConvert _) ->
       Runtime.(error ~at (ExpectedAtom j))

let mlfalse, _, _ = Typecheck.Builtin.mlfalse
let mltrue, _, _ = Typecheck.Builtin.mltrue

let as_bool ~at v =
  match v with
  | Runtime.Tag (l, []) ->
     if Runtime.equal_tag l mlfalse then
       return false
     else if Runtime.equal_tag l mltrue then
       return true
     else
     Runtime.(error ~at (BoolExpected v))

  | Runtime.(Tag (_, _::_) | Exc _ | Judgement _ | Boundary _ | Derivation _ | External _ |
             Closure _ | Handler _ | Tuple _ | Ref _ | String _) ->
     Runtime.(error ~at (BoolExpected v))

let as_handler ~at v =
  let e = Runtime.as_handler ~at v in
  return e

let as_ref ~at v =
  let e = Runtime.as_ref ~at v in
  return e

(** Main evaluation loop. *)

(** Evaluate a computation. *)
let rec comp {Location.it=c'; at} =
  match c' with
    | Syntax.Bound i ->
       Runtime.lookup_bound i

    | Syntax.Value pth ->
       Runtime.lookup_ml_value pth

    | Syntax.Function (p, c) ->
       let f v =
        Matching.match_pattern p v >>=
        begin function
        | Some us -> List.fold_left (fun c u -> Runtime.add_bound u c) (comp c) us
        | None -> Runtime.(error ~at (MatchFail v))
        end
       in
       Runtime.return_closure f

    | Syntax.MLConstructor (t, cs) ->
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

    | Syntax.MLException (exc, copt) ->
       begin match copt with
       | None ->
          let v = Runtime.Exc (exc, None) in
          return v
       | Some c ->
          comp c >>= fun v ->
          return (Runtime.Exc (exc, Some v))
       end

    | Syntax.AsDerivation cnstr ->
       Runtime.lookup_signature >>= fun sgn ->
       let drv = Nucleus.rule_as_derivation sgn cnstr in
       return (Runtime.Derivation drv)

    | Syntax.TTConstructor (cnstr, cs) ->
       Runtime.lookup_signature >>= fun sgn ->
       let rap = Nucleus.form_constructor_rap sgn cnstr in
       check_arguments ~at rap cs

    | Syntax.TTApply (c, cs) ->
       comp_as_derivation c >>= fun drv ->
       Runtime.lookup_signature >>= fun sgn ->
       let rap = Nucleus.form_derivation_rap sgn drv in
       check_arguments ~at rap cs

    | Syntax.Tuple cs ->
      let rec fold vs = function
        | [] -> return (Runtime.mk_tuple (List.rev vs))
        | c :: cs -> (comp c >>= fun v -> fold (v :: vs) cs)
      in
      fold [] cs

    | Syntax.(Handler {handler_val; handler_ops; handler_exc}) ->
        let handler_val =
          begin match handler_val with
          | [] -> None
          | _ :: _ ->
            let f v =
              match_cases ~at handler_val comp v
            in
            Some f
          end
        and handler_ops = Ident.mapi match_op_cases handler_ops
        and handler_exc = exception_handler ~at comp handler_exc
        in
        Runtime.return_handler handler_val handler_ops handler_exc

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op vs
       | c :: cs ->
          comp c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.With (c1, c2) ->
     comp c1 >>= as_handler ~at >>= fun h ->
     Runtime.handle_comp h (comp c2)

  | Syntax.Let (xcs, c) ->
     let_bind ~at xcs (comp c)

  | Syntax.LetRec (fxcs, c) ->
     letrec_bind ~at fxcs (comp c)

  | Syntax.Ref c ->
     comp c >>= fun v ->
     Runtime.mk_ref v

  | Syntax.Lookup c ->
     comp c >>= as_ref ~at >>= fun x ->
     Runtime.lookup_ref x

  | Syntax.Update (c1, c2) ->
     comp c1 >>= as_ref ~at >>= fun x ->
     comp c2 >>= fun v ->
     Runtime.update_ref x v >>= fun () ->
     Runtime.return_unit

  | Syntax.Sequence (c1, c2) ->
     comp c1 >>= fun v ->
     sequence ~at v >>= fun () ->
     comp c2

  | Syntax.Raise c ->
     comp c >>= fun v ->
     let exc = Runtime.as_exception ~at v in
     Runtime.raise_exception exc

  | Syntax.Fresh (xopt, c) ->
     comp_as_is_type c >>= fun t ->
     let x = match xopt with Some x -> x | None -> Name.mk_name "x" in
     let atm = Nucleus.fresh_atom x t in
     let v = Runtime.Judgement Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom atm))) in
     return v

  | Syntax.Meta xopt ->
     Runtime.(error ~at (MetaWithoutBoundary xopt))

  | Syntax.Match (c, cases) ->
     comp c >>=
     match_cases ~at cases comp

  | Syntax.BoundaryAscribe (c1, c2) ->
     comp_as_boundary_abstraction c2 >>= fun bdry ->
     check_judgement c1 bdry >>=
     Runtime.return_judgement

  | Syntax.Abstract (x, None, _) ->
    Runtime.(error ~at (UnannotatedAbstract x))

  | Syntax.Abstract (x, Some u, c) ->
     comp_as_is_type u >>= fun u ->
     Runtime.add_free x u
       (fun a -> comp c >>= function
        | Runtime.Judgement jdg -> Runtime.return_judgement (Nucleus.abstract_judgement a jdg)

        | Runtime.Boundary bdry -> Runtime.return_boundary (Nucleus.abstract_boundary a bdry)

        | Runtime.(Derivation _ | External  _ | Closure _ | Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
           Runtime.(error ~at (JudgementOrBoundaryExpected v)))

  | Syntax.AbstractAtom (a, c) ->
     comp_as_atom a >>= fun a ->
           begin comp c >>=
             function
             | Runtime.Judgement jdg -> Runtime.return_judgement (Nucleus.abstract_judgement a jdg)

             | Runtime.Boundary bdry -> Runtime.return_boundary (Nucleus.abstract_boundary a bdry)

             | Runtime.(External _ | Closure _ | Derivation _| Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as v ->
                Runtime.(error ~at (JudgementOrBoundaryExpected v))
           end

  | Syntax.SubstituteJudgement (c1, c2) ->
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
       | None -> Runtime.(error ~at AbstractionExpected)
       | Some t ->
          check_judgement c2 (Nucleus.abstract_not_abstract (Nucleus.form_is_term_boundary t)) >>= fun jdg ->
          begin match Nucleus.as_not_abstract jdg with
          | Some (Nucleus.JudgementIsTerm e) ->
               Runtime.lookup_signature >>= fun sgn ->
               let abstr = Nucleus.apply_judgement_abstraction sgn abstr e in
               Runtime.return_judgement abstr
          | None
          | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
             Runtime.(error ~at (IsTermExpected (Runtime.Judgement jdg)))
          end
     end

  | Syntax.SubstituteBoundary (c1, c2) ->
     comp_as_boundary_abstraction c1 >>= fun abstr ->
     begin match Nucleus.type_at_abstraction abstr with
       | None -> Runtime.(error ~at AbstractionExpected)
       | Some t ->
          check_judgement c2 (Nucleus.abstract_not_abstract (Nucleus.form_is_term_boundary t)) >>= fun jdg ->
          begin match Nucleus.as_not_abstract jdg with
          | Some (Nucleus.JudgementIsTerm e) ->
               Runtime.lookup_signature >>= fun sgn ->
               let abstr = Nucleus.apply_boundary_abstraction sgn abstr e in
               Runtime.return_boundary abstr
          | None
          | Some Nucleus.(JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _) ->
             Runtime.(error ~at (IsTermExpected (Runtime.Judgement jdg)))
          end
     end


  | Syntax.Derive (prems, c) ->
     premises prems
       (comp c >>= fun v -> let jdg = Runtime.as_judgement ~at v in return jdg)
     >>= fun (prems, concl) ->
     let drv = Nucleus.form_derivation prems concl in
     Runtime.return (Runtime.Derivation drv)

  | Syntax.Apply (c1, c2) ->
    comp c1 >>= begin function
      | Runtime.Closure f ->
        comp c2 >>= fun v ->
        Runtime.apply_closure f v
      | Runtime.(Judgement _ | Boundary _ | Derivation _ | External _ |  Handler _ | Exc _ | Tag _ | Tuple _ | Ref _ | String _) as h ->
        Runtime.(error ~at (Inapplicable h))
    end

  | Syntax.String s ->
    return (Runtime.mk_string s)

  | Syntax.Occurs (c1, c2) ->
     comp_as_atom c1 >>= fun a ->
     comp_as_judgement_abstraction c2 >>= fun abstr ->
     begin match Nucleus.occurs_judgement_abstraction a abstr with
     | true ->
        let t = Runtime.Judgement (Nucleus.(abstract_not_abstract (JudgementIsType (type_of_atom a)))) in
        return (Reflect.mk_option (Some t))
     | false ->
        return (Reflect.mk_option None)
     end

  | Syntax.Rewrite (c, cs) ->
     comp_as_judgement_abstraction c >>= fun abstr ->
     let jdg = Runtime.as_not_abstract ~at abstr in
     Runtime.get_env >>= fun env ->
     let sgn = Runtime.get_signature env in
     let rec fold abstrs = function
       | [] ->
          let abstrs = List.rev abstrs in
          let eq, jdg' = Nucleus.rewrite_judgement sgn jdg abstrs in
          let l = List.map (fun x -> Runtime.mk_judgement (Nucleus.abstract_not_abstract x)) [eq; jdg'] in
          return (Runtime.(mk_tuple l))
       | c :: cs ->
          comp_as_judgement_abstraction c >>= fun v ->
          fold (v :: abstrs) cs
     in
     fold [] cs

  | Syntax.Congruence (c1, c2, cs) ->
     comp_as_judgement_abstraction c1 >>= fun abstr1 ->
     let jdg1 = Runtime.as_not_abstract ~at abstr1 in
     comp_as_judgement_abstraction c2 >>= fun abstr2 ->
     let jdg2 = Runtime.as_not_abstract ~at abstr2 in
     Runtime.get_env >>= fun env ->
     let sgn = Runtime.get_signature env in
     let rap = Nucleus.congruence_judgement sgn jdg1 jdg2 in
     check_arguments ~at rap cs

  | Syntax.Convert (c1, c2) ->
     comp_as_judgement_abstraction c1 >>= fun jdg ->
     comp_as_eq_type_abstraction c2 >>= fun eq ->
     Runtime.get_env >>= fun env ->
     let sgn = Runtime.get_signature env in
     begin match Nucleus.convert_judgement_abstraction sgn jdg eq with
     | None -> Runtime.(error ~at (InvalidConvert (jdg, eq)))
     | Some jdg -> Runtime.return_judgement jdg
     end

  | Syntax.Context c ->
    comp_as_is_term_abstraction c >>= fun abstr ->
    let xts = Nucleus.context_is_term_abstraction abstr in
    let js =
      List.map
        (fun atm -> Runtime.Judgement Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom atm))))
        xts
    in
    return (Reflect.mk_list js)

  | Syntax.Natural c ->
    comp_as_is_term c >>= fun jdg_e ->
    Runtime.lookup_signature >>= fun signature ->
    let eq = Nucleus.natural_type_eq signature jdg_e in
    Runtime.return_judgement Nucleus.(abstract_not_abstract (JudgementEqType eq))

  | Syntax.MLBoundary bdry ->
     eval_boundary ~at bdry >>= fun bdry ->
     Runtime.return_boundary Nucleus.(abstract_not_abstract bdry)

and check_arguments ~at rap cs =
  match rap, cs with
  | Nucleus.RapDone jdg, [] -> Runtime.return_judgement (Nucleus.abstract_not_abstract jdg)
  | Nucleus.RapMore (bdry, rap_apply), c :: cs ->
     Runtime.lookup_signature >>= fun sgn ->
     check_judgement c bdry >>= fun arg ->
     let rap = rap_apply arg in
     check_arguments ~at rap cs
  | Nucleus.RapDone _, _::_ ->
     Runtime.(error ~at TooManyArguments)
  | Nucleus.RapMore _, [] ->
     Runtime.(error ~at TooFewArguments)

(** Coerce the value [v] to the given judgement boundary [bdry] *)
and coerce ~at v (bdry : Nucleus.boundary_abstraction) =
  let abstr = Runtime.as_judgement_abstraction ~at v in
  Runtime.lookup_signature >>= fun sgn ->
  Equal.coerce ~at sgn abstr bdry

(** Compute a judgement with the given abstracted boundary *)
and check_judgement ({Location.it=c'; at} as c) bdry =
  match c' with

  (* These have no use for the boundary, so we just try to coerce them after they are evaluated *)
  | Syntax.Bound _
  | Syntax.Value _
  | Syntax.Function _
  | Syntax.Handler _
  | Syntax.BoundaryAscribe _
  | Syntax.MLConstructor _
  | Syntax.TTConstructor _
  | Syntax.AsDerivation _
  | Syntax.MLException _
  | Syntax.TTApply _
  | Syntax.Tuple _
  | Syntax.With _
  | Syntax.Apply _
  | Syntax.Ref _
  | Syntax.Lookup _
  | Syntax.Update _
  | Syntax.Fresh _
  | Syntax.AbstractAtom _
  | Syntax.String _
  | Syntax.Occurs _
  | Syntax.Congruence _
  | Syntax.Rewrite _
  | Syntax.Convert _
  | Syntax.SubstituteJudgement _
  | Syntax.SubstituteBoundary _
  | Syntax.Derive _
  | Syntax.Context _
  | Syntax.Natural _
  | Syntax.MLBoundary _
  | Syntax.Raise _
    ->

    comp c >>= fun v ->
    coerce ~at v bdry

  | Syntax.Operation (op, cs) ->
     let rec fold vs = function
       | [] ->
          let vs = List.rev vs in
          Runtime.operation op ~checking:bdry vs >>= fun v ->
          coerce ~at v bdry
       | c :: cs ->
          comp c >>= fun v ->
          fold (v :: vs) cs
     in
     fold [] cs

  | Syntax.Let (xcs, c) ->
     let_bind ~at xcs (check_judgement c bdry)

  | Syntax.Sequence (c1,c2) ->
    comp c1 >>= fun v ->
    sequence ~at v >>= fun () ->
    check_judgement c2 bdry

  | Syntax.LetRec (fxcs, c) ->
     letrec_bind ~at fxcs (check_judgement c bdry)

  | Syntax.Match (c, cases) ->
     comp c >>=
     match_cases ~at cases (fun c -> check_judgement c bdry)

  | Syntax.Abstract (xopt, uopt, c) ->
    check_abstract ~at bdry xopt uopt c

  | Syntax.Meta xopt ->
     let x = match xopt with Some x -> x | None -> Name.mk_name "m" in
     let _meta, jdg = Nucleus.form_meta x bdry in
     return jdg


(** Run the abstraction [Abstract(x, uopt, c)] and check it against the boundary abstraction [bdry]. *)
and check_abstract ~at bdry x uopt c =
  match Nucleus.invert_boundary_abstraction bdry with

  | Nucleus.Stump_NotAbstract _ ->
     Runtime.(error ~at AbstractionExpected)

  | Nucleus.Stump_Abstract (a, bdry) ->
     (* NB: [a] is a fresh atom at this point. *)
     begin match uopt with

     | None ->
        Runtime.add_bound
          (Runtime.Judgement Nucleus.(abstract_not_abstract (JudgementIsTerm (form_is_term_atom a))))
          begin
            check_judgement c bdry >>= fun jdg ->
            let jdg = Nucleus.abstract_judgement ~name:x a jdg in
            return jdg
          end

     | Some ({Location.at=u_loc;_} as u) ->
        comp_as_is_type u >>= fun u ->
        let a_type = Nucleus.type_of_atom a in
        Equal.equal_type ~at:u_loc a_type u >>= fun eq (* : a_type == u *) ->
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

and exception_handler :
  'a . at:Location.t ->
       (Syntax.comp -> 'a Runtime.comp) ->
       Syntax.exception_case list -> Runtime.exc -> 'a Runtime.comp
  = fun ~at comp hnd exc ->
  let default ~at _ = Runtime.raise_exception exc in
  let v = Runtime.Exc exc in
  match_cases ~at ~default hnd comp v

and sequence ~at v =
  match v with
    | Runtime.Tuple [] -> return ()
    | _ ->
      Print.warning "@[<hov 2>%t: this value should be the unit (and why is this a runtime warning?) @]@."
        (Location.print at) ;
      return ()

and let_bind
  : 'a. at:Location.t -> Syntax.let_clause list -> 'a Runtime.comp -> 'a Runtime.comp
  = fun ~at clauses cmp ->
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
    | Syntax.Let_clause (pt, c) :: clauses ->
       comp c >>= fun v ->
       Matching.match_pattern pt v >>= begin function
        | Some us -> fold (us :: uss) clauses
        | None -> Runtime.(error ~at (MatchFail v))
       end

  in
  fold [] clauses

and letrec_bind
  : 'a . at:Location.t -> Syntax.letrec_clause list -> 'a Runtime.comp -> 'a Runtime.comp
  = fun ~at fxcs ->
  let gs =
    List.map
      (fun (Syntax.Letrec_clause (p, c)) -> (fun v ->
      Matching.match_pattern p v >>=
        begin function
        | Some us -> List.fold_left (fun c u -> Runtime.add_bound u c) (comp c) us
        | None -> Runtime.(error ~at (MatchFail v))
        end))
      fxcs
  in
  Runtime.add_bound_rec gs

(* [match_cases loc cases eval v] tries for each case in [cases] to match [v] and if
   successful continues on the computation using [eval] with the pattern variables bound.
   *)
and match_cases
  : 'a . at:Location.t -> ?default:(at:Location.t -> Runtime.value -> 'a Runtime.comp)
         -> Syntax.match_case list -> (Syntax.comp -> 'a Runtime.comp)
         -> Runtime.value -> 'a Runtime.comp
  = fun ~at ?(default=(fun ~at v -> Runtime.(error ~at (MatchFail v)))) cases eval v ->
  let bind_pattern_vars vs cmp =
    List.fold_left (fun cmp v -> Runtime.add_bound v cmp) cmp vs
  in
  let rec fold = function
    | [] -> default ~at v
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

and match_op_cases op cases =
  let rec fold cases (Runtime.{args; checking} as op_args) =
    match cases with
    | [] -> Runtime.operation op ?checking args
    | case :: cases -> match_op_case (fold cases) case op_args
  in
  fold cases

and match_op_case other (ps, ptopt, c) (Runtime.{args; checking} as op_args) =
  Matching.match_op_pattern ps ptopt args checking >>=
    function
    | Some vs -> List.fold_left (fun cmp v -> Runtime.add_bound v cmp) (comp c) vs
    | None -> other op_args

(** Run [c] and convert the result to a derivation. *)
and comp_as_derivation c =
  comp c >>= fun v -> return (Runtime.as_derivation ~at:c.Location.at v)

(** Run [c] and convert the result to an type judgement. *)
and comp_as_is_type c =
  let bdry = Nucleus.(abstract_not_abstract form_is_type_boundary) in
  check_judgement c bdry >>= fun j ->
  return (Runtime.as_is_type ~at:c.Location.at (Runtime.mk_judgement j))

(** Run [c] and convert the result to an term judgement. *)
and comp_as_is_term c =
  comp c >>= fun v -> return (Runtime.as_is_term ~at:c.Location.at v)

(** Run [c] and convert the result to a term abstraction. *)
and comp_as_is_term_abstraction c =
  comp c >>= fun v -> return (Runtime.as_is_term_abstraction ~at:c.Location.at v)

(** Run [c] and convert the result to a term abstraction. *)
(* and comp_as_is_type_abstraction c =
 *   comp c >>= fun v -> return (Runtime.as_is_type_abstraction ~at:c.Location.at v) *)

(** Run [c] and convert the result to a judgement abstraction. *)
and comp_as_judgement_abstraction c =
  comp c >>= fun v ->
  return (Runtime.as_judgement_abstraction ~at:c.Location.at v)

(** Run [c] and convert the result to a boundary abstraction. *)
and comp_as_boundary_abstraction c =
  comp c >>= fun v -> return (Runtime.as_boundary_abstraction ~at:c.Location.at v)

(** Run [c] and convert the result to a boundary. *)
and comp_as_boundary ~at c =
  comp c >>= fun v -> return (Runtime.as_boundary ~at:c.Location.at v)

(** Run [c] and convert the result to a boundary abstraction. *)
and comp_as_eq_type_abstraction c =
  comp c >>= fun v -> return (Runtime.as_eq_type_abstraction ~at:c.Location.at v)

and comp_as_atom c =
  comp c >>= fun v -> (as_atom ~at:c.Location.at v)

(** Run [c] and convert it to a boolean. *)
and comp_as_bool c =
  comp c >>= fun v -> (as_bool ~at:c.Location.at v)

and eval_boundary ~at = function
  | Syntax.BoundaryIsType ->
     Runtime.return Nucleus.(form_is_type_boundary)

  | Syntax.BoundaryIsTerm c ->
     comp_as_is_type c >>= fun t ->
     Runtime.return Nucleus.(form_is_term_boundary t)

  | Syntax.BoundaryEqType (c1, c2) ->
     comp_as_is_type c1 >>= fun t1 ->
     comp_as_is_type c2 >>= fun t2 ->
     Runtime.return Nucleus.(form_eq_type_boundary t1 t2)

  | Syntax.BoundaryEqTerm (c1, c2, c3) ->
     comp_as_is_type c3 >>= fun t ->
     Runtime.get_env >>= fun env ->
     let sgn = Runtime.get_signature env in
     let bdry = Nucleus.(abstract_not_abstract (form_is_term_boundary t)) in
     check_judgement c1 bdry >>= fun e1 ->
     let e1 =
       match Nucleus.as_is_term (Runtime.as_not_abstract ~at e1) with
       | Some e1 -> e1
       | None -> assert false
     in
     check_judgement c2 bdry >>= fun e2 ->
     let e2 =
       match Nucleus.as_is_term (Runtime.as_not_abstract ~at e2) with
       | Some e2 -> e2
       | None -> assert false
     in
     Runtime.return Nucleus.(form_eq_term_boundary sgn e1 e2)

(** Evaluation of rules *)

(* Evaluate the computation [cmp] in local context [lctx].
   Return the evaluated [lctx] and the result of [cmp]. *)
and local_context lctx cmp =
  let rec fold = function
    | [] ->
       cmp
    | (x, c) :: lctx ->
       comp_as_is_type c >>= fun t ->
       Runtime.add_free x t
         (fun a ->
              (fold lctx >>= fun abstr ->
               return (Nucleus.abstract_boundary a abstr)
         ))
  in
  fold lctx

and premise {Location.it=Syntax.Premise(x, lctx, c); at} =
  local_context lctx (comp_as_boundary_abstraction c) >>= fun bdry ->
  let mv, jdg = Nucleus.form_meta x bdry in
  let v = Runtime.Judgement jdg in
  return (mv, v)


(** Evaluate the premises of a rule, bind them to meta-variables, then evaluate
   the conclusion [cmp]. Return the evaulated premises and conclusion for
   further processing. *)
and premises :
  'a . Syntax.premise list -> 'a Runtime.comp -> (Nucleus.meta list * 'a) Runtime.comp
= fun prems cmp ->
  let rec fold prems_out = function

    | [] ->
       cmp >>= fun v ->
       let prems_out = List.rev prems_out in
       return (prems_out, v)

    | prem :: prems ->
       premise prem >>= fun (x_boundary, v) ->
       Runtime.add_bound v (fold (x_boundary :: prems_out) prems)
  in
  fold [] prems

(** Move to toplevel monad *)

let comp_value c =
  let r = comp c in
  Runtime.top_handle ~at:c.Location.at r


(** Toplevel commands *)

let (>>=) = Runtime.top_bind
let return = Runtime.top_return

let toplet_bind ~at ~quiet ~print_annot info clauses =
  let rec fold uss = function
    | [] ->
       (* parallel let: only bind at the end *)
       List.fold_left
         (List.fold_left (fun cmp u -> Runtime.top_add_ml_value u >>= fun () -> cmp))
         (return uss)
         uss

    | Syntax.Let_clause (pt, c) :: clauses ->
       comp_value c >>= fun v ->
       Matching.top_match_pattern pt v >>= begin function
        | None -> Runtime.error ~at (Runtime.MatchFail v)
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

let topletrec_bind ~at ~quiet ~print_annot info fxcs =
  let gs =
    List.map
      (fun (Syntax.Letrec_clause (p,c)) v ->
        Runtime.bind (Matching.match_pattern p v)
        begin function
        | Some us -> List.fold_left (fun c u -> Runtime.add_bound u c) (comp c) us
        | None -> Runtime.(error ~at (MatchFail v))
        end)
      fxcs
  in
  Runtime.top_add_ml_value_rec gs >>= fun () ->
  if not quiet then
    (List.iter
      (fun (f, annot) ->
        Format.printf "@[<hov 2>val %t :>@ %t@]@."
                      (Name.print f)
                      (print_annot annot))
      info) ;
  return ()

let rec toplevel ~quiet ~print_annot {Location.it=c; at} =
  match c with

  | Syntax.Rule (x, prems, bdry) ->
     Runtime.top_lookup_opens >>= fun opens ->
     Runtime.top_handle ~at (premises prems (comp_as_boundary ~at bdry)) >>= fun (premises, head) ->
     let rule = Nucleus.form_rule premises head in
     (if not quiet then
        Format.printf "@[<hov 2>Rule %t is postulated.@]@." (Ident.print ~opens ~parentheses:false x));
     Runtime.top_add_rule x rule

  | Syntax.DefMLTypeAbstract t ->
     Runtime.top_lookup_opens >>= fun opens ->
     (if not quiet then
        Format.printf "@[<hov 2>ML type %t declared.@]@." (Path.print ~opens ~parentheses:true t)) ;
     return ()

  | Syntax.DefMLType lst
  | Syntax.DefMLTypeRec lst ->
     Runtime.top_lookup_opens >>= fun opens ->
     (if not quiet then
        Format.printf "@[<hov 2>ML type%s %t declared.@]@."
          (match lst with [_] -> "" | _ -> "s")
          (Print.sequence (Path.print ~opens ~parentheses:true) "," lst)) ;
     return ()

  | Syntax.DeclOperation (op, k) ->
     Runtime.top_lookup_opens >>= fun opens ->
     (if not quiet then
        Format.printf "@[<hov 2>Operation %t is declared.@]@."
          (Path.print ~opens ~parentheses:true op)) ;
     return ()

  | Syntax.DeclException (exc, topt) ->
     Runtime.top_lookup_opens >>= fun opens ->
     (if not quiet then
        Format.printf "@[<hov 2>Exception %t is declared.@]@."
          (Path.print ~opens ~parentheses:true exc)) ;
     return ()

  | Syntax.DeclExternal (x, sch, s) ->
     begin
       match External.lookup s with
       | None -> Runtime.error ~at (Runtime.UnknownExternal s)
       | Some v ->
          Runtime.top_add_ml_value v >>= (fun () ->
           if not quiet then
             Format.printf "@[<hov 2>external %t :@ %t = \"%s\"@]@."
               (Name.print x)
               (print_annot () sch)
               s ;
           return ())
     end

  | Syntax.TopLet (info, clauses) ->
     let print_annot = print_annot () in
     toplet_bind ~at ~quiet ~print_annot info clauses

  | Syntax.TopLetRec (info, fxcs) ->
     let print_annot = print_annot () in
     topletrec_bind ~at ~quiet ~print_annot info fxcs

  | Syntax.TopWith cases ->
     let rec fold = function
       | [] -> return ()
       | (op, case) :: cases ->
          let case other = match_op_case other case in
          Runtime.top_add_handle ~at op case >>= fun () ->
          fold cases
     in
     fold cases

  | Syntax.TopComputation (c, sch) ->
     comp_value c >>= fun v ->
     Runtime.top_lookup_penv >>= fun penv ->
     if not quiet then
       Format.printf "@[<hov 2>- :>@ %t@ =@ %t@]@."
           (print_annot () sch)
           (Runtime.print_value ~penv v) ;
     return ()

  | Syntax.Open pth ->
     Runtime.top_open_path pth

  | Syntax.MLModule (mdl_name, cmds) ->
     if not quiet then Format.printf "@[<hov 2>Processing module %t@]@." (Name.print mdl_name) ;
     Runtime.top_as_ml_module (toplevels ~quiet ~print_annot cmds)

  | Syntax.Verbosity i -> Config.verbosity := i; return ()

and toplevels ~quiet ~print_annot =
  Runtime.top_fold
    (fun () -> toplevel ~quiet ~print_annot)
    ()
