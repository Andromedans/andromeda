(** Type-directed equality checking based on user-provided rules. *)

open Eqchk_common

(** Normalization *)

(** Extract an optional value, or declare a normalization fail *)
let deopt x err =
  match x with
  | None -> raise (EqchkError (Normalization_fail err))
  | Some x -> x

(** The types of beta rules. *)

type normalizer =
  { type_computations : (Patt.is_type * Nucleus.eq_type Nucleus.rule) list SymbolMap.t ;
    type_heads : IntSet.t SymbolMap.t ;
    term_computations : (Patt.is_term * Nucleus.eq_term Nucleus.rule) list SymbolMap.t ;
    term_heads : IntSet.t SymbolMap.t
  }

let empty_normalizer =
  { type_computations = SymbolMap.empty ;
    type_heads = SymbolMap.empty ;
    term_computations = SymbolMap.empty ;
    term_heads = SymbolMap.empty }

(** The type of extensionality rules. *)
type equation =
  { ext_pattern : Patt.is_type (* the rewrite pattern to match the type of equality *)
  ; ext_rule : Nucleus.eq_term Nucleus.rule (* the associated rule *)
  }


(* An equality checker is given by beta rules and extensionality rules. We organize them
   as maps taking a symbol to a list of rules which have that symbol at the head. This
   allows us to quickly determine which rules are potentially applicable. *)
   type checker = {
    normalizer : normalizer ;
    ext_rules : equation list SymbolMap.t ;
  }

  let empty_checker =
    { normalizer = empty_normalizer ;
      ext_rules = SymbolMap.empty }

let find_type_computations sym {type_computations;_} =
  SymbolMap.find_opt sym type_computations

let find_term_computations sym {term_computations;_} =
  SymbolMap.find_opt sym term_computations


(** Functions [make_XYZ] convert a derivation to a rewrite rule, or raise the exception [Invalid_rule] when the derivation
    has the wrong form. *)

let make_type_computation drv =
  let rec fold k ~equations = function

    | Nucleus_types.(Conclusion eq)  ->
       let (Nucleus_types.EqType (_asmp, t1, _t2)) = Nucleus.expose_eq_type eq in
       let patt =  Eqchk_pattern.make_is_type k t1 in
       let s = head_symbol_type t1 in
       (s, patt)

    | Nucleus_types.(Premise ({meta_boundary=bdry;_} as m, drv)) ->
       if ((is_object_premise bdry) && not equations) || (not (is_object_premise bdry) && equations) then
         fold (k+1) ~equations drv
       else
         if (not (is_object_premise bdry) && not equations) then
           fold (k+1) ~equations:true drv
         else
           raise (EqchkError (Invalid_rule (ObjectPremiseAfterEqualityPremise(m))))
  in
  let drv =
    match Nucleus.as_eq_type_rule drv with
    | Some drv -> drv
    | None -> raise (EqchkError (Invalid_rule TypeEqualityConclusionExpected))
  in
  let (s, patt) = fold 0 ~equations:false (Nucleus.expose_rule drv) in
  s, (patt, drv)


let make_term_computation drv =
  let rec fold k ~equations = function

    | Nucleus_types.(Conclusion eq) ->
       let (Nucleus_types.EqTerm (_asmp, e1, _e2, _t)) = Nucleus.expose_eq_term eq in
       let patt = Eqchk_pattern.make_is_term k e1 in
       let s = head_symbol_term e1 in
       (s, patt)

    | Nucleus_types.(Premise ({meta_boundary=bdry;_} as m, drv)) ->
       if ((is_object_premise bdry) && not equations) || (not (is_object_premise bdry) && equations) then
         fold (k+1) ~equations drv
       else
         if (not (is_object_premise bdry) && not equations) then
           fold (k+1) ~equations:true drv
         else
           raise (EqchkError (Invalid_rule (ObjectPremiseAfterEqualityPremise(m))))
  in
  let drv =
    match Nucleus.as_eq_term_rule drv with
    | Some drv -> drv
    | None -> raise (EqchkError (Invalid_rule TermEqualityConclusionExpected))
  in
  let (s, patt) = fold 0 ~equations:false (Nucleus.expose_rule drv) in
  s, (patt, drv)


let add_type_computation_norm normalizer drv =
  let sym, bt = make_type_computation drv in
  let rls =
    match find_type_computations sym normalizer with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  sym, bt,
  { normalizer with type_computations = SymbolMap.add sym rls normalizer.type_computations }


let add_term_computation_norm normalizer drv =
  let sym, bt = make_term_computation drv in
  let rls =
    match find_term_computations sym normalizer with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  sym, bt,
  { normalizer with term_computations = SymbolMap.add sym rls normalizer.term_computations }

let set_type_heads_norm nrm sym heads =
  { nrm with type_heads = SymbolMap.add sym heads nrm.type_heads }

let set_term_heads_norm normalizer sym heads =
  { normalizer with term_heads = SymbolMap.add sym heads normalizer.term_heads }

let get_type_heads chk sym =
  match SymbolMap.find_opt sym chk.normalizer.type_heads with
  | None -> IntSet.empty
  | Some hs -> hs

let get_term_heads chk sym =
  match SymbolMap.find_opt sym chk.normalizer.term_heads with
  | None -> IntSet.empty
  | Some hs -> hs

(** Functions that apply rewrite rules *)

(** Find a type computation rule and apply it to [t]. *)
let rec apply_type_beta chk sgn t =
  let s = head_symbol_type (Nucleus.expose_is_type t) in
  let betas = chk.normalizer.type_computations in
  match SymbolMap.find_opt s betas with

  | None -> None

  | Some lst ->
     let rec fold = function
       | [] -> None

       | (patt, rl) :: lst ->
          begin match Eqchk_pattern.match_is_type sgn t patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_type_rap sgn rl in
             try
              let rap' = rap_apply rap args in
              let t_eq_t' = resolve_rap chk sgn IntSet.empty rap' in
              Some t_eq_t'
             with
               | Fatal_error _ -> fold lst
          end
     in
     fold lst


(** Find a term computation rule and apply it to [e]. *)
and apply_term_beta chk sgn e =
  let s = head_symbol_term (Nucleus.expose_is_term e) in
  let betas = chk.normalizer.term_computations in
  match SymbolMap.find_opt s betas with

  | None -> None

  | Some lst ->
     let rec fold = function
       | [] -> None

       | (patt, rl) :: lst ->
          begin match Eqchk_pattern.match_is_term sgn e patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_term_rap sgn rl in
             try
              let rap' = rap_apply rap args in
              let e_eq_e' = resolve_rap chk sgn IntSet.empty rap' in
              Some e_eq_e'
             with
               | Fatal_error _ -> fold lst
          end
     in
     fold lst

(** Normalize a type *)
and normalize_type_norm ~strong sgn chk ty0 =
  let rec fold ty0_eq_ty1 ty1 =
    let ty1_eq_ty2, Normal ty2 = normalize_heads_type ~strong sgn chk ty1 in
    let ty0_eq_ty2 = Nucleus.transitivity_type ty0_eq_ty1 ty1_eq_ty2 in

    match apply_type_beta chk sgn ty2 with

    | None -> ty0_eq_ty2, Normal ty2

    | Some ty2_eq_ty3 ->
       let (Nucleus.Stump_EqType (_, _, ty3)) = Nucleus.invert_eq_type ty2_eq_ty3 in
       let ty0_eq_ty3 = Nucleus.transitivity_type ty0_eq_ty2 ty2_eq_ty3 in
       fold ty0_eq_ty3 ty3
  in
  fold (Nucleus.reflexivity_type ty0) ty0


and normalize_term_norm ~strong sgn chk e0 =
  let rec fold e0_eq_e1 e1 =
    let e1_eq_e2, Normal e2 = normalize_heads_term ~strong sgn chk e1 in
    let e0_eq_e2 = Nucleus.transitivity_term e0_eq_e1 e1_eq_e2 in

    match apply_term_beta chk sgn e2 with

    | None -> e0_eq_e2, Normal e2

    | Some e2_eq_e3 ->
       let (Nucleus.Stump_EqTerm (_, _, e3, _)) = Nucleus.invert_eq_term sgn e2_eq_e3 in
       (* XXX normalize heads somewhere *)
       (* XXX this will fail because e_eq_e' and e'_eq_e'' may happen at different types *)
       (* XXX figure out how to convert e'_eq_e'' using Nucleus.convert_eq_term *)
       let e0_eq_e3 = Nucleus.transitivity_term e0_eq_e2 e2_eq_e3 in
       fold e0_eq_e3 e3
  in
  fold (Nucleus.reflexivity_term sgn e0) e0


(* Normalize those arguments of [ty0] which are considered to be normalizing. *)
and normalize_heads_type ~strong sgn chk ty0 =
  match Nucleus.invert_is_type sgn ty0 with

    | Nucleus.Stump_TypeConstructor (s, cargs) ->
      let heads = get_type_heads chk (Ident s) in
      let cargs_eq_cargs', Normal cargs' = normalize_arguments ~strong sgn chk heads cargs in
      let ty0_eq_ty1, ty1 = Nucleus.rewrite_is_type sgn ty0 cargs_eq_cargs' in
      ty0_eq_ty1, Normal ty1

    | Nucleus.Stump_TypeMeta (mv, es) ->
      let heads = get_type_heads chk (Nonce (Nucleus.meta_nonce mv)) in
      let es = List.map (fun e -> Nucleus.(abstract_not_abstract (JudgementIsTerm e))) es in
      let es_eq_es', Normal es' = normalize_arguments ~strong sgn chk heads es in
      let ty0_eq_ty1, ty1 = Nucleus.rewrite_is_type sgn ty0 es_eq_es' in
      ty0_eq_ty1, Normal ty1


(* Normalize those arguments of [e0] which are considered to be normalizing. *)
and normalize_heads_term ~strong sgn chk e0 =
  match Nucleus.invert_is_term sgn e0 with

  | Nucleus.Stump_TermConstructor (s, cargs) ->
     let heads = get_term_heads chk (Ident s) in
     let cargs_eq_cargs', Normal cargs' = normalize_arguments ~strong sgn chk heads cargs in
     let e0_eq_e1, e1 = Nucleus.rewrite_is_term sgn e0 cargs_eq_cargs' in
    e0_eq_e1, Normal e1

  | Nucleus.Stump_TermMeta (mv, es) ->
     let heads = get_term_heads chk (Nonce (Nucleus.meta_nonce mv)) in
     let es = List.map (fun e -> Nucleus.(abstract_not_abstract (JudgementIsTerm e))) es in
     let es_eq_es', Normal es' = normalize_arguments ~strong sgn chk heads es in
     let e0_eq_e1, e1 = Nucleus.rewrite_is_term sgn e0 es_eq_es' in
    e0_eq_e1, Normal e1

  | Nucleus.Stump_TermAtom _ ->
     Nucleus.(reflexivity_term sgn e0), Normal e0

  | Nucleus.Stump_TermConvert (e0', t) (* == e0 : t *) ->
     let e0'_eq_e1, Normal e1 = normalize_heads_term ~strong sgn chk e0' in (* e0' == e1 : t' *)
     (* e0 == e0 : t and e0' == e1 : t' ===> e0 == e1 : t *)
     let e0_eq_e1 = Nucleus.transitivity_term (Nucleus.reflexivity_term sgn e0) e0'_eq_e1 in
     (* let e1 = Nucleus.form_is_term_convert sgn e1 t in *)
     let Nucleus.Stump_EqTerm (_, _, e1, _) = Nucleus.invert_eq_term sgn e0_eq_e1 in
     (* e0' == e1 : t *)
     e0_eq_e1, Normal e1

(** Normalize arguments [args] and convert them along previously normalized arguments [conv_args]. Then apply rule application [rap]. *)
and normalize_arguments ~strong sgn chk heads args =
  let rec fold k args' args_eq_args' args_rest =
    match args_rest with

    | [] ->
      List.rev args_eq_args', Normal (List.rev args')

    | arg :: args_rest ->
      if strong || IntSet.mem k heads
      then
       let arg_eq_arg', Normal arg' = normalize_argument ~strong sgn chk arg in
       fold (k+1) (arg' :: args') (arg_eq_arg' :: args_eq_args') args_rest
      else
        let arg_eq_arg' = deopt (Nucleus.reflexivity_judgement_abstraction sgn arg) (EqualityArgument arg) in
        fold (k+1) (arg :: args') (arg_eq_arg' :: args_eq_args') args_rest
  in
  fold 0 [] [] args


and normalize_argument ~strong sgn chk arg =
  match (Nucleus.invert_judgement_abstraction arg) with

  | Nucleus.Stump_Abstract (atm, arg) ->
     let arg_eq_arg', Normal arg'= normalize_argument ~strong sgn chk arg in
     let arg' = Nucleus.abstract_judgement atm arg'
     and arg_eq_arg' = Nucleus.abstract_judgement atm arg_eq_arg' in
     arg_eq_arg', Normal arg'

  | Nucleus.(Stump_NotAbstract (JudgementIsType t)) ->
      let t_eq_t', Normal t' = normalize_type_norm ~strong sgn chk t in
      Nucleus.(abstract_not_abstract (JudgementEqType t_eq_t')),
      Normal (Nucleus.(abstract_not_abstract (JudgementIsType t')))

  | Nucleus.(Stump_NotAbstract (JudgementIsTerm e)) ->
      let e_eq_e', Normal e' = normalize_term_norm ~strong sgn chk e in
      Nucleus.(abstract_not_abstract (JudgementEqTerm  e_eq_e')),
      Normal (Nucleus.(abstract_not_abstract (JudgementIsTerm e')))

  | Nucleus.(Stump_NotAbstract (JudgementEqType eqty)) ->
      raise (EqchkError (Normalization_fail (EqualityTypeArguement eqty)))
  | Nucleus.(Stump_NotAbstract (JudgementEqTerm eqtm)) ->
      raise (EqchkError (Normalization_fail (EqualityTermArguement eqtm)))

(** Type-directed phase of equality checking *)

and make_equation drv =

  (* Check that e is the bound meta-variable k *)
  let check_meta k e =
    match e with
    | Nucleus_types.(TermMeta (MetaBound j, [])) -> if j <> k then raise (EqchkError (Invalid_rule (WrongMetavariable (k, j))))
    | Nucleus_types.(TermMeta (MetaFree _, _) | TermMeta (MetaBound _, _::_) | TermBoundVar _ | TermAtom _ |
                     TermConstructor _ | TermConvert _) ->
       raise (EqchkError (Invalid_rule (BoundMetavariableExpected (k, e))))
  in

  (* Extract a type from an optional boundary *)
  let extract_type = function
    | Some (Nucleus_types.(NotAbstract (BoundaryIsTerm t))) -> t
    | Some (Nucleus_types.(Abstract _ ) as abst) -> raise (EqchkError (Invalid_rule (TermBoundaryExpectedGotAbstraction abst)))
    | Some (Nucleus_types.(NotAbstract (BoundaryIsType _ | BoundaryEqType _ | BoundaryEqTerm _ as b ))) ->
      raise (EqchkError (Invalid_rule (TermBoundaryExpected b)))
    | None ->
       raise (EqchkError (Invalid_rule (TermBoundaryNotGiven)))
  in

  (* do the main work where:
     n_ob counts leading object premises, n_eq counts trailing equality premises,
     (bdry1opt, bdry2opt) are the last two seen object premise boundaries
  *)
  let rec fold (bdry1opt, bdry2opt) n_ob n_eq = function

    | Nucleus_types.(Conclusion eq) ->
       let (Nucleus_types.EqTerm (_asmp, e1, e2, t)) = Nucleus.expose_eq_term eq in
       begin
       try (* check LHS *)
         check_meta (n_eq+1) e1
       with
         EqchkError( Invalid_rule _ ) -> raise (EqchkError (Invalid_rule (EquationLHSnotCorrect (eq, n_eq + 1))))
       end ;
       begin
       try (* check RHS *)
         check_meta n_eq e2
       with
          EqchkError ( Invalid_rule _ ) -> raise (EqchkError (Invalid_rule (EquationRHSnotCorrect (eq, n_eq))))
       end ;
       let t1 = extract_type bdry1opt in
       let t1' = Shift_meta.is_type (n_eq+2) t1
       and t2' = Shift_meta.is_type (n_eq+1) (extract_type bdry2opt) in
       (* check that types are equal *)
       if not (Alpha_equal.is_type t1' t) || not (Alpha_equal.is_type t2' t) then raise (EqchkError (Invalid_rule (TypeOfEquationMismatch (eq, t1', t2')))); ;
       let patt = Eqchk_pattern.make_is_type (n_ob-2) t1 in
       let s = head_symbol_type t1 in
       (s, patt)

    | Nucleus_types.(Premise ({meta_boundary=bdry;_} as p, drv)) ->
       if is_object_premise bdry then
         begin
           if n_eq > 0 then raise (EqchkError (Invalid_rule (ObjectPremiseAfterEqualityPremise p)));
           fold (bdry2opt, Some bdry) (n_ob + 1) n_eq drv
         end
       else
         fold (bdry1opt, bdry2opt) n_ob (n_eq + 1) drv
  in

  (* Put the derivation into the required form *)
  let drv =
    match Nucleus.as_eq_term_rule drv with
    | Some drv -> drv
    | None -> raise ( EqchkError(Invalid_rule (DerivationWrongForm drv)))
  in
  (* Collect head symbol and pattern (and verify that drv has the correct form) *)
  let s, patt = fold (None, None) 0 0 (Nucleus.expose_rule drv) in
  s, { ext_pattern = patt; ext_rule = drv }

(** Find an extensionality rule for [e1 == e2 : t], if there is one, return a rule
   application that will prove it. *)
and find ext_eqs sgn bdry =
  let (e1, e2, t) = Nucleus.invert_eq_term_boundary bdry in
  match SymbolMap.find_opt (head_symbol_type (Nucleus.expose_is_type t)) ext_eqs with
  | None -> None
  | Some lst ->
     let rec fold = function
       | [] -> None
       | {ext_pattern=patt; ext_rule=rl} :: lst ->
          begin match Eqchk_pattern.match_is_type sgn t patt with
          | None -> fold lst
          | Some args ->
             let rap = Nucleus.form_eq_term_rap sgn rl in
             let arg1 = Nucleus.(abstract_not_abstract (JudgementIsTerm e1))
             and arg2 = Nucleus.(abstract_not_abstract (JudgementIsTerm e2)) in
             try
               Some (rap_apply rap (args @ [arg1; arg2]))
             with
              | Fatal_error _ -> fold lst
          end
     in
     fold lst


(** Types and functions for manipulation of rules. *)


(** General equality checking functions *)

(** An equality to be proved is given by a (possibly abstracted) equality boundary. The
   functions [prove_XYZ] receive such a boundary and attempt to prove the corresponding
   equality. *)

and prove_eq_type_abstraction chk sgn abstr =
  let rec fold abstr =
    match Nucleus.invert_eq_type_boundary_abstraction abstr with

    | Nucleus.Stump_NotAbstract eq ->
       Nucleus.(abstract_not_abstract ((prove_eq_type chk sgn eq)))

    | Nucleus.Stump_Abstract (atm, abstr) ->
       let abstr = fold abstr in
       Nucleus.abstract_eq_type atm abstr
  in
  fold abstr

and prove_eq_term_abstraction chk sgn abstr =
  let rec fold abstr =
    match Nucleus.invert_eq_term_boundary_abstraction abstr with

    | Nucleus.Stump_NotAbstract bdry ->
       Nucleus.(abstract_not_abstract ((prove_eq_term ~ext:true chk sgn bdry)))

    | Nucleus.Stump_Abstract (atm, abstr) ->
       let abstr = fold abstr in
       Nucleus.abstract_eq_term atm abstr
  in
  fold abstr

and prove_eq_type chk sgn (ty1, ty2) =
  let ty1_eq_ty1', ty1' = normalize_type_norm ~strong:false sgn chk ty1
  and ty2_eq_ty2', ty2' = normalize_type_norm ~strong:false sgn chk ty2 in
  let ty1'_eq_ty2' = check_normal_type chk sgn ty1' ty2' in
  Nucleus.transitivity_type
    (Nucleus.transitivity_type ty1_eq_ty1' ty1'_eq_ty2')
    (Nucleus.symmetry_type ty2_eq_ty2')


and prove_eq_term ~ext chk sgn bdry =
  let normalization_phase bdry =
     let (e1, e2, t) = Nucleus.invert_eq_term_boundary bdry in
     let e1_eq_e1', Normal e1' = normalize_term_norm ~strong:false sgn chk e1
     and e2_eq_e2', Normal e2' = normalize_term_norm ~strong:false sgn chk e2 in
     let e1'_eq_e2' = check_normal_term chk sgn (Normal e1') (Normal e2') in
     Nucleus.transitivity_term
       (Nucleus.transitivity_term e1_eq_e1' e1'_eq_e2')
       (Nucleus.symmetry_term e2_eq_e2')
  in

  if not ext then
    normalization_phase bdry
  else
    let (e1, e2, t) = Nucleus.invert_eq_term_boundary bdry in
    let t_eq_t', Normal t' = normalize_type_norm ~strong:false sgn chk t in
    let e1' = Nucleus.(form_is_term_convert sgn e1 t_eq_t')
    and e2' = Nucleus.(form_is_term_convert sgn e2 t_eq_t')in
    let bdry' = Nucleus.(form_eq_term_boundary sgn e1' e2') in
    let bdry =
    match Nucleus.(as_eq_term_boundary bdry' ) with
    | Some bdry -> bdry
    | None -> assert false
    in
    let eq_jdg =
    match find chk.ext_rules sgn bdry with

    | Some rap ->
       (* reduce the problem to an application of an extensionality rule *)
       resolve_rap chk sgn IntSet.empty rap

    | None -> normalization_phase bdry

    in
    let t'_eq_t = Nucleus.(symmetry_type t_eq_t') in
    Nucleus.(form_eq_term_convert eq_jdg t'_eq_t)



and check_normal_type chk sgn (Normal ty1) (Normal ty2) =
  match Nucleus.congruence_is_type sgn ty1 ty2 with

  | None -> raise (EqchkError(Equality_fail (NoCongruenceTypes (ty1, ty2)) ))

  | Some rap ->
     let sym = head_symbol_type (Nucleus.expose_is_type ty1) in
     let hs = get_type_heads chk sym in
     resolve_rap chk sgn hs rap

(* We assume that [e1] and [e2] have the same type. *)
and check_normal_term chk sgn (Normal e1) (Normal e2) =
  match Nucleus.congruence_is_term sgn e1 e2 with

  | None -> raise (EqchkError (Equality_fail (NoCongruenceTerms (e1, e2))))

  | Some rap ->
     let sym = head_symbol_term (Nucleus.expose_is_term e1) in
     let hs = get_term_heads chk sym in
     resolve_rap chk sgn hs rap


(** Given a rule application, fill in the missing premises, as long as they
    are equations. *)
and resolve_rap :
  'a . checker -> Nucleus.signature -> IntSet.t -> 'a Nucleus.rule_application -> 'a
  = fun chk sgn heads rap ->
  let rec fold k = function

    | Nucleus.RapDone ty1_eq_ty2 -> ty1_eq_ty2

    | Nucleus.RapMore (bdry, rap) ->
       let eq = prove_boundary_abstraction ~ext:(not (IntSet.mem k heads)) chk sgn bdry
       in
       fold (k+1) (rap eq)
  in
  fold 0 rap

(* Prove an abstracted equality boundary. The [ext] flag tells us whether
   we should proceed wither with the type-directed phase or or the normalization-phase. *)
and prove_boundary_abstraction ~ext chk sgn bdry =
  let rec prove bdry =
  match Nucleus.invert_boundary_abstraction bdry with

  | Nucleus.(Stump_NotAbstract (BoundaryEqType eq)) ->
     Nucleus.(abstract_not_abstract (JudgementEqType (prove_eq_type chk sgn eq)))

  | Nucleus.(Stump_NotAbstract (BoundaryEqTerm eq)) ->
     Nucleus.(abstract_not_abstract (JudgementEqTerm (prove_eq_term ~ext chk sgn eq)))

  | Nucleus.Stump_Abstract (atm, bdry) ->
     let eq_abstr = prove bdry in
     Nucleus.abstract_judgement atm eq_abstr

  | Nucleus.(Stump_NotAbstract (BoundaryIsTerm _ | BoundaryIsType _)) ->
    raise (Fatal_error ("cannot prove an object boundary"))

  in
  prove bdry

(** The exported form of normalization for types *)
let normalize_type ~strong chk sgn t =
  let eq, Normal t = normalize_type_norm ~strong sgn chk t in
  eq, t

(** The exported form of normalization for terms *)
let normalize_term ~strong chk sgn e =
  let eq, Normal e = normalize_term_norm ~strong sgn chk e in
  eq, e

let set_type_heads ({normalizer; _} as chk) s hs =
  { chk with normalizer = set_type_heads_norm normalizer (Ident s) (IntSet.of_list hs) }

let set_term_heads ({normalizer; _} as chk) s hs =
  { chk with normalizer = set_term_heads_norm normalizer (Ident s) (IntSet.of_list hs) }

(** The [add_XYZ] functions add a new rule, computed from the given derivation, to the
   given checker, or raise [Invalid_rule] if not possible. *)

let add_type_computation' checker drv =
  let sym, bt, normalizer = add_type_computation_norm checker.normalizer drv in
   sym, bt, {checker with normalizer}

let add_type_computation checker drv =
  match add_type_computation' checker drv with
  | _, _, checker -> checker

let add_term_computation' checker drv =
  let sym, bt, normalizer = add_term_computation_norm checker.normalizer drv in
  sym, bt, {checker with normalizer}

let add_term_computation checker drv =
  match add_term_computation' checker drv with
  | (_, _, checker) -> checker

let add_extensionality' checker drv =
  let sym, bt = make_equation drv in
  let rls =
    match SymbolMap.find_opt sym checker.ext_rules with
    | None -> [bt]
    | Some rls -> rls @ [bt]
  in
  (sym, {checker with ext_rules = SymbolMap.add sym rls checker.ext_rules})


let add_extensionality checker drv =
  match add_extensionality' checker drv with
  | (_, checker) -> checker

let add ~quiet ~penv chk drv =
  try
    match add_extensionality' chk drv with
    | (sym, chk) ->
      if not quiet then
        Format.printf "Extensionality rule for %t:@ %t@."
          (print_symbol ~penv sym)
          (Nucleus.print_derivation ~penv drv) ;
      chk

  with
    | EqchkError ( Invalid_rule _ ) ->
      try
        begin match add_type_computation' chk drv with

        |  (sym, ((patt, _), _), chk) ->
            let heads = heads_type patt in
            let chk = { chk with normalizer = set_type_heads_norm chk.normalizer sym heads } in
            if not quiet then
              Format.printf "@[<hov 2>Type computation rule for %t (heads at [%t]):@\n%t@.@]"
                (print_symbol ~penv sym)
                (Print.sequence (fun k ppf -> Format.fprintf ppf "%d" k) "," (IntSet.elements heads))
                (Nucleus.print_derivation ~penv drv) ;
            chk
        end

     with
      | EqchkError ( Invalid_rule _ ) ->
          begin match add_term_computation' chk drv with
            | (sym, ((patt, _), _), chk) ->
              let heads = heads_term patt in
              let chk = { chk with normalizer = set_term_heads_norm chk.normalizer sym heads } in
              if not quiet then
                Format.printf "@[<hov 2>Term computation rule for %t (heads at [%t]):@\n%t\n@.@]"
                  (print_symbol ~penv sym)
                  (Print.sequence (fun k ppf -> Format.fprintf ppf "%d" k) "," (IntSet.elements heads))
                  (Nucleus.print_derivation ~penv drv) ;
              chk
          end
