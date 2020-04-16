(** Formation of judgements from rules *)

open Nucleus_types

let form_alpha_equal_type t1 t2 =
  match Alpha_equal.is_type t1 t2 with
  | false -> None
  | true -> Some (Mk.eq_type Assumption.empty t1 t2)

(** Compare two terms for alpha equality. *)
let form_alpha_equal_term sgn e1 e2 =
  let t1 = Sanity.type_of_term sgn e1
  and t2 = Sanity.type_of_term sgn e2
  in
  (* XXX if e1 and e2 are α-equal, we may apply uniqueness of typing to
     conclude that their types are equal, so we don't have to compute t1, t2,
     and t1 =α= t2. *)
  match Alpha_equal.is_type t1 t2 with
  | false -> Error.raise (AlphaEqualTypeMismatch (t1, t2))
  | true ->
     begin match Alpha_equal.is_term e1 e2 with
     | false -> None
     | true ->
        (* We may keep the assumptions empty here. One might worry
           that the assumptions needed for [e2 : t2] have to be included,
           but this does not seem to be the case: we have [e2 : t2] and
           [t1 == t2] (without assumptions as they are alpha-equal!),
           hence by conversion [e2 : t1], and whatever assumptions are
           required for [e2 : t2], they're already present in [e2]. *)
        Some (Mk.eq_term Assumption.empty e1 e2 t1)
     end

let rec form_alpha_equal_abstraction equal_u abstr1 abstr2 =
  match abstr1, abstr2 with
  | NotAbstract u1, NotAbstract u2 ->
     begin match equal_u u1 u2 with
     | None -> None
     | Some eq -> Some (Mk.not_abstract eq)
     end
  | Abstract (x1, t1, abstr1), Abstract (x2, t2, abstr2) ->
     let x = Name.prefer x1 x2 in
     begin match Alpha_equal.is_type t1 t2 with
     | false -> None
     | true ->
        begin match form_alpha_equal_abstraction equal_u abstr1 abstr2 with
        | None -> None
        | Some eq -> Some (Mk.abstract x t1 eq)
        end
     end
  | (NotAbstract _, Abstract _)
  | (Abstract _, NotAbstract _) -> None


(** Partial rule applications *)

(** Form a rule application for the given constructor [c] *)
let form_constructor_rap sgn c =
  let rec fold args = function
    | Premise ({meta_boundary=prem;_}, rl) ->
       let bdry = Instantiate_meta.abstraction Form_rule.instantiate_premise ~lvl:0 args prem in
       let rap abstr =
         if not (Check.judgement_boundary_abstraction sgn abstr bdry)
         then Error.raise InvalidArgument ;
         let arg = Coerce.to_argument abstr in
         let args = arg :: args in
         fold args rl
       in
       RapMore (bdry, rap)

    | Conclusion (BoundaryIsType ()) ->
       RapDone (JudgementIsType (Mk.type_constructor c (Indices.to_list args)))

    | Conclusion (BoundaryIsTerm _) ->
       RapDone (JudgementIsTerm (Mk.term_constructor c (Indices.to_list args)))

    | Conclusion (BoundaryEqType (lhs_schema, rhs_schema)) ->
         (* order of arguments not important in [Collect_assumptions.arguments],
            we could try avoiding a list reversal caused by [Indices.to_list]. *)
         let asmp = Collect_assumptions.arguments (Indices.to_list args)
         and lhs = Instantiate_meta.is_type ~lvl:0 args lhs_schema
         and rhs = Instantiate_meta.is_type ~lvl:0 args rhs_schema
         in
         RapDone (JudgementEqType (Mk.eq_type asmp lhs rhs))

    | Conclusion (BoundaryEqTerm (e1_schema, e2_schema, t_schema)) ->
         (* order of arguments not important in [Collect_assumptions.arguments],
            we could try avoiding a list reversal caused by [Indices.to_list]. *)
         let asmp = Collect_assumptions.arguments (Indices.to_list args)
         and e1 = Instantiate_meta.is_term ~lvl:0 args e1_schema
         and e2 = Instantiate_meta.is_term ~lvl:0 args e2_schema
         and t = Instantiate_meta.is_type ~lvl:0 args t_schema
         in
         RapDone (JudgementEqTerm (Mk.eq_term asmp e1 e2 t))
  in
  let rl = Signature.lookup_rule c sgn in
  fold [] rl

(** Form a meta-variable application for the given meta-variable [mv] *)
let form_meta_rap sgn mv =
  let rec fold es = function

    | Abstract (_, t, bdry) ->
       let t = Instantiate_bound.is_type_fully ~lvl:0 es t in
       let t_bdry = NotAbstract (BoundaryIsTerm t) in
       let rap = function
         | NotAbstract (JudgementIsTerm e) ->
            if not (Check.is_term_boundary sgn e t)
            then Error.raise InvalidArgument ;
            let es = e :: es in
            fold es bdry
         | Abstract _
         | NotAbstract (JudgementIsType _ | JudgementEqType _ | JudgementEqTerm _)
           -> Error.raise InvalidArgument
       in
       RapMore (t_bdry, rap)

    | NotAbstract bdry ->
       let args = List.rev es in
       let jdg =
         match bdry with
         | BoundaryIsType _ -> JudgementIsType (Mk.type_meta (MetaFree mv) args)
         | BoundaryIsTerm _ -> JudgementIsTerm (Mk.term_meta (MetaFree mv) args)
         | BoundaryEqType (t1, t2) ->
            let t1 = Instantiate_bound.is_type_fully ~lvl:0 es t1
            and t2 = Instantiate_bound.is_type_fully ~lvl:0 es t2 in
            JudgementEqType (Mk.eq_type_meta (MetaFree mv) t1 t2)
         | BoundaryEqTerm (e1, e2, t) ->
            let e1 = Instantiate_bound.is_term_fully ~lvl:0 es e1
            and e2 = Instantiate_bound.is_term_fully ~lvl:0 es e2
            and t = Instantiate_bound.is_type_fully ~lvl:0 es t in
            JudgementEqTerm (Mk.eq_term_meta (MetaFree mv) e1 e2 t)
       in
       RapDone jdg
  in
  fold [] mv.meta_boundary

(** Form a rap from a rule *)
let form_rule_rap sgn inst rl =
  let rec fold args = function
    | Premise ({meta_boundary=prem;_}, drv) ->
       let bdry = Instantiate_meta.abstraction Form_rule.instantiate_premise ~lvl:0 args prem in
       let rap abstr =
         if not (Check.judgement_boundary_abstraction sgn abstr bdry)
         then Error.raise InvalidArgument ;
         let arg = Coerce.to_argument abstr in
         let args = arg :: args in
         fold args drv
       in
       RapMore (bdry, rap)

    | Conclusion concl ->
       let concl = inst args concl in
       RapDone concl
  in
  fold [] rl

let form_derivation_rap sgn drv =
  form_rule_rap sgn (Instantiate_meta.judgement ~lvl:0) drv

let form_is_type_rap sgn drv =
  form_rule_rap sgn (Instantiate_meta.is_type ~lvl:0) drv

let form_is_term_rap sgn drv =
  form_rule_rap sgn (Instantiate_meta.is_term ~lvl:0) drv

let form_eq_type_rap sgn drv =
  form_rule_rap sgn (Instantiate_meta.eq_type ~lvl:0) drv

let form_eq_term_rap sgn drv =
  form_rule_rap sgn (Instantiate_meta.eq_term ~lvl:0) drv

(* A rather finicky and dangerous operation that directly makes a derivation out
   of a primitive rule, by directly manipulating bound meta-variables. *)
let rule_as_derivation sgn cnstr =
  (* look up the rule *)
  let rl = Signature.lookup_rule cnstr sgn in
  (* compute the arity of the rule *)
  let arity =
    let rec count = function
      | Conclusion _ -> 0
      | Premise (_, bdry) -> 1 + count bdry
    in
    count rl
  in
  let rec fold k args = function
    | Conclusion bdry ->
       let args = List.rev args in
       let jdg =
         match bdry with
         | BoundaryIsType () -> JudgementIsType (Mk.type_constructor cnstr args)
         | BoundaryIsTerm _ -> JudgementIsTerm (Mk.term_constructor cnstr args)
         | BoundaryEqType (t1, t2) ->
            let asmp = Collect_assumptions.arguments args in
            JudgementEqType (Mk.eq_type asmp t1 t2)
         | BoundaryEqTerm (e1, e2, t) ->
            let asmp = Collect_assumptions.arguments args in
            JudgementEqTerm (Mk.eq_term asmp e1 e2 t)
       in
       Conclusion jdg

    | Premise (prem, bdry) ->
       (* compute the k-th argument *)
       let rec mk_arg i args = function
         | NotAbstract bdry ->
            let args = List.rev args in
            let jdg =
              match bdry with
              | BoundaryIsType () -> JudgementIsType (Mk.type_meta (MetaBound k) args)
              | BoundaryIsTerm _ -> JudgementIsTerm (Mk.term_meta (MetaBound k) args)
              | BoundaryEqType (t1, t2) ->
                 let t1 = Shift_meta.is_type (k+1) t1
                 and t2 = Shift_meta.is_type (k+1) t2 in
                 let asmp = Collect_assumptions.term_arguments ~lvl:k args in
                 JudgementEqType (Mk.eq_type asmp t1 t2)
              | BoundaryEqTerm (e1, e2, t) ->
                 let e1 = Shift_meta.is_term (k+1) e1
                 and e2 = Shift_meta.is_term (k+1) e2
                 and t = Shift_meta.is_type (k+1) t in
                 let asmp = Collect_assumptions.term_arguments ~lvl:k args in
                 JudgementEqTerm (Mk.eq_term asmp e1 e2 t)
            in
            Arg_NotAbstract jdg
         | Abstract (x, t, bdry) ->
            let args = (TermBoundVar i) :: args in
            Arg_Abstract (x, mk_arg (i+1) args bdry)
       in
       let arg = mk_arg 0 [] prem.meta_boundary in
       let drv = fold (k-1) (arg :: args) bdry in
       Premise (prem, drv)
  in
  fold (arity-1) [] rl

(** Formation of a term from an atom *)
let form_is_term_atom = Mk.atom

(** Conversion *)

let form_is_term_convert_opt sgn e (EqType (asmp, t1, t2)) =
  match e with
  | TermConvert (e, asmp0, t0) ->
     if Alpha_equal.is_type t0 t1 then
       (* here we rely on transitivity of equality *)
       let asmp = Assumption.union asmp0 (Assumption.union asmp (Collect_assumptions.is_type t1))
       (* we could have used the assumptions of [t0] instead, because [t0] and [t1] are
            alpha equal, and so either can derive the type. Possible optimizations:
              (i) pick the smaller of the assumptions of [t0] or of [t1],
             (ii) pick the asumptions that are included in [t2]
            (iii) remove assumptions already present in [t2] from the assumption set
       *)
       in
       (* [e] itself is not a [TermConvert] by the maintained invariant. *)
       Some (Mk.term_convert e asmp t2)
     else
       None

  | (TermAtom _ | TermBoundVar _ | TermConstructor _ | TermMeta _) as e ->
     let t0 = Sanity.natural_type sgn e in
     if Alpha_equal.is_type t0 t1 then
       (* We need not include assumptions of [t1] because [t0] is alpha-equal
            to [t1] so we can use [t0] in place of [t1] if so desired. *)
       (* [e] is not a [TermConvert] by the above pattern-check *)
       Some (Mk.term_convert e asmp t2)
     else
       None

let form_is_term_convert sgn e (EqType (_, t1, _) as eq) =
  match form_is_term_convert_opt sgn e eq with
  | Some e -> e
  | None ->
     let t0 = Sanity.natural_type sgn e in
     Error.raise (InvalidConvert (t0, t1))

let form_eq_term_convert_opt (EqTerm (asmp1, e1, e2, t0)) (EqType (asmp2, t1, t2)) =
  if Alpha_equal.is_type t0 t1 then
    (* We could have used the assumptions of [t0] instead of [t1], see comments in [form_is_term]
       about possible optimizations. *)
    let asmp = Assumption.union asmp1 (Assumption.union asmp2 (Collect_assumptions.is_type t1)) in
    Some (Mk.eq_term asmp e1 e2 t2)
  else
    None

let form_eq_term_convert (EqTerm (_, _, _, t0) as eq1) (EqType (_, t1, _) as eq2) =
  match form_eq_term_convert_opt eq1 eq2 with
  | Some eq -> eq
  | None -> Error.raise (InvalidConvert (t0, t1))

let reflexivity_type t = Mk.eq_type Assumption.empty t t

let reflexivity_term sgn e =
  let t = Sanity.type_of_term sgn e in
  Mk.eq_term Assumption.empty e e t


exception ObjectJudgementExpected

let reflexivity_judgement_abstraction sgn abstr =
  let rec fold abstr =
    match Invert.invert_judgement_abstraction abstr with

    | Stump_Abstract (atm, abstr) ->
       let abstr = fold abstr in
       Abstract.judgement_abstraction atm abstr

    | Stump_NotAbstract (JudgementIsType t) ->
       Abstract.not_abstract (JudgementEqType (reflexivity_type t))

    | Stump_NotAbstract (JudgementIsTerm e) ->
       Abstract.not_abstract (JudgementEqTerm (reflexivity_term sgn e))

    | Stump_NotAbstract (JudgementEqType _ | JudgementEqTerm _) ->
       raise ObjectJudgementExpected
  in
  try
    Some (fold abstr)
  with
  | ObjectJudgementExpected -> None


let symmetry_term (EqTerm (asmp, e1, e2, t)) = Mk.eq_term asmp e2 e1 t

let symmetry_type (EqType (asmp, t1, t2)) = Mk.eq_type asmp t2 t1

let transitivity_term (EqTerm (asmp, e1, e2, t)) (EqTerm (asmp', e1', e2', t')) =
  match Alpha_equal.is_term e2 e1' with
  | false -> Error.raise (AlphaEqualTermMismatch (e2, e1'))
  | true ->
     let asmp = Assumption.union asmp (Assumption.union asmp' (Collect_assumptions.is_term e1'))
     in Mk.eq_term asmp e1 e2' t

let transitivity_term' (EqTerm (asmp, e1, e2, t)) (EqTerm (asmp', e1', e2', t')) =
  match Alpha_equal.is_term e2 e1' with
  | false -> Error.raise (AlphaEqualTermMismatch (e2, e1'))
  | true ->
     let asmp = Assumption.union asmp (Assumption.union asmp' (Collect_assumptions.is_term e2))
     in Mk.eq_term asmp e1 e2' t'

let transitivity_type (EqType (asmp1, t1, t2)) (EqType (asmp2, u1, u2)) =
  let penv = Nucleus_types.({
    forbidden = Name.set_empty ;
    debruijn_var = [] ;
    debruijn_meta = [] ;
    opens = Path.set_empty
  }) in
  Format.printf "Are types %t and %t alpha-equal to apply transitivity of types?@." Nucleus_print.(thesis_is_type ~penv t2) Nucleus_print.(thesis_is_type ~penv u1);
  begin match Alpha_equal.is_type t2 u1 with
  | false -> Error.raise (AlphaEqualTypeMismatch (t2, u1))
  | true ->
     (* XXX could use assumptions of [u1] instead, or whichever is better. *)
     let asmp = Assumption.union asmp1 (Assumption.union asmp2 (Collect_assumptions.is_type t2))
     in Mk.eq_type asmp t1 u2
  end

(** Formation of boundaries *)

let form_is_type_boundary = BoundaryIsType ()

let form_is_term_boundary t = BoundaryIsTerm t

let form_eq_type_boundary t1 t2 = BoundaryEqType (t1, t2)

let form_eq_term_boundary sgn e1 e2 =
  let t1 = Sanity.type_of_term sgn e1
  and t2 = Sanity.type_of_term sgn e2 in
  if Alpha_equal.is_type t1 t2 then
    BoundaryEqTerm (e1, e2, t1)
  else
    Error.raise (AlphaEqualTypeMismatch (t1, t2))

let rec form_is_term_boundary_abstraction = function

  | NotAbstract t ->
     NotAbstract (form_is_term_boundary t)

  | Abstract (x, t, abstr) ->
     Abstract (x, t, form_is_term_boundary_abstraction abstr)
